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

#include "share.hpp"

namespace bp {

share::share(const hash_digest& work_hash, const uint32_t nonce,
    const uint64_t extra_nonce, const hash_digest& merkle_root,
    uint64_t timestamp, const data_chunk& hub_pubkey,
    const data_chunk& miner_pubkey, const data_chunk& tor_service_pubkey,
    hash_list shares)
    : work_hash_(work_hash)
    , nonce_(nonce)
    , extra_nonce_(extra_nonce)
    , merkle_root_(merkle_root)
    , timestamp_(timestamp)
    , hub_pubkey_(hub_pubkey)
    , miner_pubkey_(miner_pubkey)
    , tor_service_pubkey_(tor_service_pubkey)
    , shares_(shares)
{
}

const hash_digest& share::work_hash() const { return this->work_hash_; }

}
