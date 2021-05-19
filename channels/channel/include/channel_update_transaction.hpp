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

#ifndef CHANNEL_UPDATE_TRANSACTION_HPP
#define CHANNEL_UPDATE_TRANSACTION_HPP

#include "channel_transaction.hpp"

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

// Channel update transaction for one way channel management.
class channel_update_transaction : public channel_transaction {
public:
    // Create a payment update to the channel. Arguments are the same
    // as the funding transaction, apart from spending from UTXO, this
    // spends from fund transaction
    channel_update_transaction(const transaction& fund_transaction,
        const ec_public& hub, const ec_public& miner,
        const ec_public& hub_noncoop, const ec_public& miner_noncoop,
        const hash_digest& secret);
};
}

#endif
