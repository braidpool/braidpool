/**
 * Copyright (c) 2021 d11dpool developers (see AUTHORS)
 *
 * This file is part of d11dpool.
 *
 * d11dpool is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * d11dpool is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with d11dpool.  If not, see <https://www.gnu.org/licenses/>.
 */

#ifndef ONE_WAY_CHANNEL_HPP
#define ONE_WAY_CHANNEL_HPP

#include <string.h>

#include <bitcoin/bitcoin.hpp>

using namespace bc::system;
using namespace bc::system::wallet;
using namespace bc::system::chain;

class one_way_channel
{
public:
    one_way_channel(const ec_private& ours, const ec_public& theirs);

    transaction& fund_transaction(const hash_digest& input_tx_hash,
        const unint32_t input_index);

    transaction& refund_transaction(const hash_digest& tx_hash,
        const unint32_t index);

    transaction& channel_update_transaction(const hash_digest& tx_hash,
        const unint32_t index);
}


#endif
