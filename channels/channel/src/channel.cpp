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

#include <string.h>
#include <iostream>

#include "channel.hpp"

using namespace bc;
using namespace bc::wallet;
using namespace bc::chain;

transaction
one_way_channel::fund_transaction(const hash_digest& input_tx_hash,
        const uint32_t input_index, const ec_public& hub, const ec_public& miner,
    const ec_public& hub_noncoop, const ec_public& miner_noncoop, const hash_digest& secret)
{
    // TODO: Implement
    return transaction{};
}

transaction
one_way_channel::refund_transaction(const transaction& fund_transaction,
    const payment_address hub_address)
{
    // TODO: Implement
    return transaction{};
}


transaction
one_way_channel::channel_update_transaction(const transaction& fund_transaction,
    const ec_public& hub, const ec_public& miner, const ec_public& hub_noncoop,
    const ec_public& miner_noncoop, const hash_digest& secret)
{
    // TODO: Implement
    return transaction{};
}

