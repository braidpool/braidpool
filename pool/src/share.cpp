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

share::share() { }

share::share(hash_digest&& work_hash, uint32_t nonce, uint64_t extra_nonce,
    hash_digest&& merkle_root, uint64_t timestamp, data_chunk&& hub_pubkey,
    data_chunk&& miner_pubkey, data_chunk&& tor_service_pubkey,
    hash_list&& shares)
    : work_hash_(std::move(work_hash))
    , nonce_(nonce)
    , extra_nonce_(extra_nonce)
    , merkle_root_(std::move(merkle_root))
    , timestamp_(timestamp)
    , hub_pubkey_(std::move(hub_pubkey))
    , miner_pubkey_(std::move(miner_pubkey))
    , tor_service_pubkey_(std::move(tor_service_pubkey))
    , shares_(std::move(shares))
{
}
}
