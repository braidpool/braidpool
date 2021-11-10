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

namespace bp {

using namespace libbitcoin::system;

// Encapsulate a share for a given work
class share {
public:
    share(const hash_digest& work_hash, const uint32_t nonce,
        const uint64_t extra_nonce, const hash_digest& merkle_root,
        uint64_t timestamp, const data_chunk& hub_pubkey,
        const data_chunk& miner_pubkey, const data_chunk& tor_service_pubkey,
        hash_list shares);

    const hash_digest& work_hash() const;

private:
    const hash_digest& work_hash_;
    uint32_t nonce_;
    uint64_t extra_nonce_;
    const hash_digest& merkle_root_;
    const uint64_t timestamp_;
    const data_chunk& hub_pubkey_;
    const data_chunk& miner_pubkey_;
    const data_chunk& tor_service_pubkey_;
    hash_list shares_;
};
}

#endif
