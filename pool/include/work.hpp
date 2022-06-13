/**
 * Copyright (c) 2021 braidpool developers (see AUTHORS)
 *
 * This file is part of braidpool.
 *
 * braidpool is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * braidpool is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with braidpool.  If not, see <https://www.gnu.org/licenses/>.
 */

#ifndef BP_WORK_HPP
#define BP_WORK_HPP

#include <bitcoin/system.hpp>
#include <cstdint>
#include <msgpack.hpp>

namespace bp {

using namespace libbitcoin::system;

// Class to encapsulate the work that miners use to generate shares.
// The conversion of getblocktemplate to block is not covered by this
// class.
class work {
 public:
  // msgpack requires default constructor
  work();
  work(uint32_t version, hash_digest&& previous_block_hash, uint64_t difficulty,
       std::string&& coinbase, hash_list&& transactions);

  uint32_t version() const { return version_; }

  uint64_t difficulty() const { return difficulty_; }

  const hash_digest& previous_block_hash() const {
    return previous_block_hash_;
  }

  const std::string& coinbase() const { return coinbase_; }

  const hash_list& transactions() const { return transactions_; }

  MSGPACK_DEFINE(version_, previous_block_hash_, difficulty_, coinbase_);

 private:
  uint32_t version_;
  hash_digest previous_block_hash_;
  uint64_t difficulty_;
  std::string coinbase_;
  hash_list transactions_;
};
}  // namespace bp

#endif
