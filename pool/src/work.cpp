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

#include "work.hpp"

namespace bp {

work::work(const uint32_t version, const hash_digest& previous_block_hash,
    const uint64_t difficulty, const std::string& coinbase,
    chain::transaction::list&& transactions)
    : version_(version)
    , previous_block_hash_(previous_block_hash)
    , difficulty_(difficulty)
    , coinbase_(coinbase)
    , transactions_(std::move(transactions))
{
}

uint32_t work::version() const { return this->version_; }

uint64_t work::difficulty() const { return this->difficulty_; }

const hash_digest& work::previous_block_hash() const
{
    return this->previous_block_hash_;
}

const std::string& work::coinbase() const { return this->coinbase_; }
}
