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

#ifndef BP_SHARE_HPP
#define BP_SHARE_HPP

#include <bitcoin/system.hpp>
#include <msgpack.hpp>

namespace bp {

using namespace libbitcoin::system;

// Encapsulate a share for a given work
class share {
 public:
  // msgpack requires default constructor
  share();
  share(hash_digest&& work_hash, uint32_t nonce, uint64_t extra_nonce,
        hash_digest&& merkle_root, uint64_t timestamp, data_chunk&& hub_pubkey,
        data_chunk&& miner_pubkey, data_chunk&& tor_service_pubkey,
        hash_list&& shares);

  const hash_digest& work_hash() const { return work_hash_; }

  uint32_t nonce() const { return nonce_; }

  uint64_t extra_nonce() const { return extra_nonce_; }

  const hash_digest& merkle_root() const { return merkle_root_; }

  uint64_t timestamp() const { return timestamp_; }
  const data_chunk& hub_pubkey() const { return hub_pubkey_; }
  const data_chunk& miner_pubkey() const { return miner_pubkey_; }
  const data_chunk& tor_service_pubkey() const { return tor_service_pubkey_; }
  const hash_list& shares() const { return shares_; }

  MSGPACK_DEFINE(work_hash_, nonce_, extra_nonce_, merkle_root_, timestamp_,
                 hub_pubkey_, miner_pubkey_, tor_service_pubkey_, shares_);

 private:
  hash_digest work_hash_;
  uint32_t nonce_;
  uint64_t extra_nonce_;
  hash_digest merkle_root_;
  uint64_t timestamp_;
  data_chunk hub_pubkey_;
  data_chunk miner_pubkey_;
  data_chunk tor_service_pubkey_;
  hash_list shares_;
};
}  // namespace bp

#endif
