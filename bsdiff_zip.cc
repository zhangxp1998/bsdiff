// Copyright 2026
// ZIP-aware bsdiff entry matching.

#include "bsdiff/bsdiff.h"

#include <err.h>
#include <stdint.h>
#include <string.h>

#include <algorithm>
#include <limits>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "bsdiff/diff_encoder.h"
#include "bsdiff/logging.h"
#include "bsdiff/patch_writer.h"
#include "bsdiff/suffix_array_index_interface.h"

namespace bsdiff {
namespace {

uint16_t ReadLE16(const uint8_t* p) {
  return static_cast<uint16_t>(p[0]) | (static_cast<uint16_t>(p[1]) << 8);
}

uint32_t ReadLE32(const uint8_t* p) {
  return static_cast<uint32_t>(p[0]) | (static_cast<uint32_t>(p[1]) << 8) |
         (static_cast<uint32_t>(p[2]) << 16) |
         (static_cast<uint32_t>(p[3]) << 24);
}

constexpr uint32_t kZipLocalFileHeaderSignature = 0x04034b50;
constexpr uint32_t kZipCentralDirectorySignature = 0x02014b50;
constexpr uint32_t kZipEndOfCentralDirectorySignature = 0x06054b50;
constexpr uint32_t kZip32Max = 0xffffffffU;

struct ZipEntry {
  std::string name;
  size_t local_header_offset{0};
  size_t data_offset{0};
  size_t compressed_size{0};
};

struct ZipFileIndex {
  std::vector<ZipEntry> entries;
};

bool AddIfInBounds(size_t a, size_t b, size_t limit, size_t* out) {
  if (a > limit || b > limit - a)
    return false;
  *out = a + b;
  return true;
}

bool FindEndOfCentralDirectory(const uint8_t* buf,
                               size_t size,
                               size_t* eocd_offset) {
  if (size < 22)
    return false;
  const size_t max_comment = 0xffff;
  const size_t min_offset = size > 22 + max_comment ? size - 22 - max_comment : 0;
  for (size_t pos = size - 22;; --pos) {
    if (ReadLE32(buf + pos) == kZipEndOfCentralDirectorySignature) {
      const uint16_t comment_len = ReadLE16(buf + pos + 20);
      if (pos + 22 + comment_len == size) {
        *eocd_offset = pos;
        return true;
      }
    }
    if (pos == min_offset)
      break;
  }
  return false;
}

bool ParseZipEntries(const uint8_t* buf, size_t size, ZipFileIndex* zip) {
  zip->entries.clear();

  size_t eocd_offset = 0;
  if (!FindEndOfCentralDirectory(buf, size, &eocd_offset))
    return false;

  const uint16_t total_entries_disk = ReadLE16(buf + eocd_offset + 8);
  const uint16_t total_entries = ReadLE16(buf + eocd_offset + 10);
  const uint32_t cd_size32 = ReadLE32(buf + eocd_offset + 12);
  const uint32_t cd_offset32 = ReadLE32(buf + eocd_offset + 16);

  // Keep this first implementation deliberately ZIP32-only. ZIP64 archives
  // fall back to normal bsdiff instead of risking a corrupt patch.
  if (total_entries_disk != total_entries || cd_size32 == kZip32Max ||
      cd_offset32 == kZip32Max || total_entries == 0xffff)
    return false;

  const size_t cd_offset = cd_offset32;
  const size_t cd_size = cd_size32;
  size_t cd_end = 0;
  if (!AddIfInBounds(cd_offset, cd_size, size, &cd_end) || cd_end > eocd_offset)
    return false;

  size_t pos = cd_offset;
  for (uint16_t i = 0; i < total_entries; ++i) {
    if (pos + 46 > cd_end || ReadLE32(buf + pos) != kZipCentralDirectorySignature)
      return false;

    const uint32_t compressed_size32 = ReadLE32(buf + pos + 20);
    const uint32_t local_header_offset32 = ReadLE32(buf + pos + 42);
    const uint16_t name_len = ReadLE16(buf + pos + 28);
    const uint16_t extra_len = ReadLE16(buf + pos + 30);
    const uint16_t comment_len = ReadLE16(buf + pos + 32);

    size_t name_offset = pos + 46;
    size_t extra_offset = 0;
    size_t comment_offset = 0;
    size_t next_pos = 0;
    if (!AddIfInBounds(name_offset, name_len, cd_end, &extra_offset) ||
        !AddIfInBounds(extra_offset, extra_len, cd_end, &comment_offset) ||
        !AddIfInBounds(comment_offset, comment_len, cd_end, &next_pos))
      return false;

    if (compressed_size32 != kZip32Max && local_header_offset32 != kZip32Max) {
      const size_t local = local_header_offset32;
      if (local + 30 <= size &&
          ReadLE32(buf + local) == kZipLocalFileHeaderSignature) {
        const uint16_t local_name_len = ReadLE16(buf + local + 26);
        const uint16_t local_extra_len = ReadLE16(buf + local + 28);
        size_t data_offset = 0;
        size_t data_end = 0;
        if (AddIfInBounds(local + 30, local_name_len, size, &data_offset) &&
            AddIfInBounds(data_offset, local_extra_len, size, &data_offset) &&
            AddIfInBounds(data_offset, compressed_size32, size, &data_end)) {
          ZipEntry entry;
          entry.name.assign(reinterpret_cast<const char*>(buf + name_offset),
                            name_len);
          entry.local_header_offset = local;
          entry.data_offset = data_offset;
          entry.compressed_size = compressed_size32;
          zip->entries.push_back(std::move(entry));
        }
      }
    }

    pos = next_pos;
  }

  return pos == cd_end;
}

std::string OccurrenceKey(const std::string& name, size_t occurrence) {
  std::string key = name;
  key.push_back('\0');
  key.append(std::to_string(occurrence));
  return key;
}

std::map<std::string, const ZipEntry*> BuildEntryMap(
    const std::vector<ZipEntry>& entries) {
  std::map<std::string, const ZipEntry*> result;
  std::map<std::string, size_t> counts;
  for (const auto& entry : entries) {
    size_t occurrence = counts[entry.name]++;
    result.emplace(OccurrenceKey(entry.name, occurrence), &entry);
  }
  return result;
}

struct MatchedEntrySegment {
  const ZipEntry* old_entry{nullptr};
  const ZipEntry* new_entry{nullptr};
};

class LocalSuffixArrayCache {
 public:
  explicit LocalSuffixArrayCache(SuffixArrayIndexInterface** external_cache)
      : external_cache_(external_cache) {}

  ~LocalSuffixArrayCache() {
    if (!external_cache_)
      delete local_cache_;
  }

  SuffixArrayIndexInterface** ptr() {
    return external_cache_ ? external_cache_ : &local_cache_;
  }

 private:
  SuffixArrayIndexInterface** external_cache_{nullptr};
  SuffixArrayIndexInterface* local_cache_{nullptr};
};

class OffsetPatchWriter : public PatchWriterInterface {
 public:
  OffsetPatchWriter(PatchWriterInterface* patch,
                    size_t old_base,
                    int64_t* global_old_pos)
      : patch_(patch),
        old_base_(old_base),
        global_old_pos_(global_old_pos) {}

  bool Init(size_t /* new_size */) override { return true; }

  bool WriteDiffStream(const uint8_t* data, size_t size) override {
    return patch_->WriteDiffStream(data, size);
  }

  bool WriteExtraStream(const uint8_t* data, size_t size) override {
    return patch_->WriteExtraStream(data, size);
  }

  bool AddControlEntry(const ControlEntry& entry) override {
    if (entry.diff_size > 0) {
      if (local_old_pos_ < 0)
        return false;
      const uint64_t desired_u64 = old_base_ +
          static_cast<uint64_t>(local_old_pos_);
      if (desired_u64 > static_cast<uint64_t>(std::numeric_limits<int64_t>::max()))
        return false;
      const int64_t desired = static_cast<int64_t>(desired_u64);
      const int64_t move = desired - *global_old_pos_;
      if (move != 0) {
        if (!patch_->AddControlEntry(ControlEntry(0, 0, move)))
          return false;
        *global_old_pos_ = desired;
      }
      if (!patch_->AddControlEntry(entry))
        return false;
      *global_old_pos_ += static_cast<int64_t>(entry.diff_size) +
                          entry.offset_increment;
    } else if (entry.extra_size > 0) {
      // The old-file pointer is irrelevant for an extra-only block. Do not emit
      // the local offset increment; the next diff block will explicitly move to
      // the right global source offset if needed.
      if (!patch_->AddControlEntry(ControlEntry(0, entry.extra_size, 0)))
        return false;
    } else if (entry.offset_increment != 0) {
      // Pure local seek. Delay it until the next diff block, where it can be
      // converted into an absolute global move.
    }

    local_old_pos_ += static_cast<int64_t>(entry.diff_size) +
                      entry.offset_increment;
    return true;
  }

  bool Close() override { return true; }

 private:
  PatchWriterInterface* patch_{nullptr};
  size_t old_base_{0};
  int64_t* global_old_pos_{nullptr};
  int64_t local_old_pos_{0};
};

bool EmitFallbackDiff(const uint8_t* old_buf,
                      size_t oldsize,
                      const uint8_t* new_buf,
                      size_t newsize,
                      size_t min_length,
                      PatchWriterInterface* patch,
                      int64_t* global_old_pos,
                      SuffixArrayIndexInterface** sai_cache) {
  if (newsize == 0)
    return true;
  OffsetPatchWriter offset_patch(patch, 0, global_old_pos);
  return bsdiff(old_buf, oldsize, new_buf, newsize, min_length, &offset_patch,
                sai_cache) == 0;
}

bool EmitEntryDiff(const uint8_t* old_buf,
                   const uint8_t* new_buf,
                   const ZipEntry& old_entry,
                   const ZipEntry& new_entry,
                   size_t min_length,
                   PatchWriterInterface* patch,
                   int64_t* global_old_pos) {
  if (new_entry.compressed_size == 0)
    return true;

  const uint8_t* old_data = old_buf + old_entry.data_offset;
  const uint8_t* new_data = new_buf + new_entry.data_offset;
  if (old_entry.compressed_size == new_entry.compressed_size &&
      memcmp(old_data, new_data, new_entry.compressed_size) == 0) {
    const uint64_t desired_u64 = old_entry.data_offset;
    if (desired_u64 > static_cast<uint64_t>(std::numeric_limits<int64_t>::max()))
      return false;
    const int64_t desired = static_cast<int64_t>(desired_u64);
    const int64_t move = desired - *global_old_pos;
    if (move != 0) {
      if (!patch->AddControlEntry(ControlEntry(0, 0, move)))
        return false;
      *global_old_pos = desired;
    }

    if (!patch->AddControlEntry(ControlEntry(new_entry.compressed_size, 0, 0)))
      return false;
    std::vector<uint8_t> zeros(std::min<size_t>(new_entry.compressed_size,
                                                1024 * 1024), 0);
    size_t remaining = new_entry.compressed_size;
    while (remaining > 0) {
      const size_t chunk = std::min(remaining, zeros.size());
      if (!patch->WriteDiffStream(zeros.data(), chunk))
        return false;
      remaining -= chunk;
    }
    *global_old_pos += static_cast<int64_t>(new_entry.compressed_size);
    return true;
  }

  OffsetPatchWriter offset_patch(patch, old_entry.data_offset, global_old_pos);
  return bsdiff(old_data, old_entry.compressed_size, new_data,
                new_entry.compressed_size, min_length, &offset_patch,
                nullptr) == 0;
}

std::vector<MatchedEntrySegment> FindMatchedEntrySegments(
    const ZipFileIndex& old_zip,
    const ZipFileIndex& new_zip) {
  std::vector<MatchedEntrySegment> matched;
  auto old_map = BuildEntryMap(old_zip.entries);
  std::map<std::string, size_t> new_counts;

  for (const auto& new_entry : new_zip.entries) {
    const size_t occurrence = new_counts[new_entry.name]++;
    auto it = old_map.find(OccurrenceKey(new_entry.name, occurrence));
    if (it == old_map.end())
      continue;
    if (new_entry.compressed_size == 0 || it->second->compressed_size == 0)
      continue;
    matched.push_back(MatchedEntrySegment{it->second, &new_entry});
  }

  std::sort(matched.begin(), matched.end(), [](const MatchedEntrySegment& a,
                                               const MatchedEntrySegment& b) {
    return a.new_entry->data_offset < b.new_entry->data_offset;
  });

  std::vector<MatchedEntrySegment> non_overlapping;
  size_t last_end = 0;
  for (const auto& segment : matched) {
    const size_t start = segment.new_entry->data_offset;
    const size_t end = start + segment.new_entry->compressed_size;
    if (start < last_end)
      continue;
    non_overlapping.push_back(segment);
    last_end = end;
  }
  return non_overlapping;
}

}  // namespace

int bsdiff_zip(const uint8_t* old_buf,
               size_t oldsize,
               const uint8_t* new_buf,
               size_t newsize,
               const char* patch_filename,
               SuffixArrayIndexInterface** sai_cache) {
  BsdiffPatchWriter patch(patch_filename);
  return bsdiff_zip(old_buf, oldsize, new_buf, newsize, 0, &patch, sai_cache);
}

int bsdiff_zip(const uint8_t* old_buf,
               size_t oldsize,
               const uint8_t* new_buf,
               size_t newsize,
               PatchWriterInterface* patch,
               SuffixArrayIndexInterface** sai_cache) {
  return bsdiff_zip(old_buf, oldsize, new_buf, newsize, 0, patch, sai_cache);
}

int bsdiff_zip(const uint8_t* old_buf,
               size_t oldsize,
               const uint8_t* new_buf,
               size_t newsize,
               size_t min_length,
               PatchWriterInterface* patch,
               SuffixArrayIndexInterface** sai_cache) {
  ZipFileIndex old_zip;
  ZipFileIndex new_zip;
  if (!ParseZipEntries(old_buf, oldsize, &old_zip) ||
      !ParseZipEntries(new_buf, newsize, &new_zip)) {
    return bsdiff(old_buf, oldsize, new_buf, newsize, min_length, patch,
                  sai_cache);
  }

  std::vector<MatchedEntrySegment> matched =
      FindMatchedEntrySegments(old_zip, new_zip);
  if (matched.empty()) {
    return bsdiff(old_buf, oldsize, new_buf, newsize, min_length, patch,
                  sai_cache);
  }

  if (!patch->Init(newsize))
    return 1;

  // Fallback regions are diffed against the full old file. Cache that suffix
  // array across all fallback regions; otherwise ZIPs with many entries would
  // rebuild the same full-file suffix array for every local header gap.
  LocalSuffixArrayCache fallback_sai_cache(sai_cache);

  int64_t global_old_pos = 0;
  size_t new_pos = 0;
  for (const auto& segment : matched) {
    const size_t segment_start = segment.new_entry->data_offset;
    if (segment_start > new_pos) {
      if (!EmitFallbackDiff(old_buf, oldsize, new_buf + new_pos,
                            segment_start - new_pos, min_length, patch,
                            &global_old_pos, fallback_sai_cache.ptr()))
        return 1;
    }

    if (!EmitEntryDiff(old_buf, new_buf, *segment.old_entry, *segment.new_entry,
                       min_length, patch, &global_old_pos))
      return 1;
    new_pos = segment_start + segment.new_entry->compressed_size;
  }

  if (new_pos < newsize) {
    if (!EmitFallbackDiff(old_buf, oldsize, new_buf + new_pos,
                          newsize - new_pos, min_length, patch,
                          &global_old_pos, fallback_sai_cache.ptr()))
      return 1;
  }

  if (!patch->Close())
    errx(1, "Closing the zip-aware patch file");

  return 0;
}

}  // namespace bsdiff
