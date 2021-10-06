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

#ifndef WORK_HPP
#define WORK_HPP

#include <bitcoin/system.hpp>
#include <cstdint>

namespace bp {

using namespace libbitcoin::system;

// Class to encapsulate the work that miners use to generate shares.
// The conversion of getblocktemplate to block is not covered by this
// class.
class work {
public:
    work(const uint32_t version, const hash_digest& previous_block_hash,
        const uint64_t difficulty, const std::string& coinbase,
        chain::transaction::list&& transactions);

    uint32_t version() const;
    uint64_t difficulty() const;
    const hash_digest& previous_block_hash() const;
    const std::string& coinbase() const;

private:
    const uint32_t version_;
    const hash_digest& previous_block_hash_;
    const uint64_t difficulty_;
    const std::string coinbase_;
    chain::transaction::list&& transactions_;
};
}

#endif
