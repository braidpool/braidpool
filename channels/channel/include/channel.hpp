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

#include <bitcoin/system.hpp>

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

// Creates transactions for one way channel management.
// Transactions types are fund, refund, channel updates and channel close.
class one_way_channel
{
public:
    // Create a funding transaction given the input points, hub's and
    // miner's co-operative and not co-operative public keys, as well
    // as the hash of the preimage
    // output: if 1 (2 of 2 H and M) else (2 of 2 H' and M' and secret equalverify)
    transaction fund_transaction(const hash_digest& input_tx_hash,
        const uint32_t input_index, const std::string& script_sig,
        const ec_public& hub, const ec_public& miner,
        const ec_public& hub_noncoop, const ec_public& miner_noncoop,
        const hash_digest& secret, uint64_t value);

    // Create a refund transaction given the funding transaction and
    // the hub's address
    transaction refund_transaction(const transaction& fund_transaction,
        const payment_address hub_address);

    // Create a payment update to the channel. Arguments are the same
    // as the funding transaction, apart from spending from UTXO, this
    // spends from fund transaction
    transaction channel_update_transaction(const transaction& fund_transaction,
        const ec_public& hub, const ec_public& miner,
        const ec_public& hub_noncoop, const ec_public& miner_noncoop,
        const hash_digest& secret);

private:

    void push_2of2_multisig(operation::list& ops, const ec_public& key_1,
        const ec_public& key_2);

    operation::list make_fund_output(const ec_public& hub,
        const ec_public& miner, const ec_public& hub_noncoop,
        const ec_public& miner_noncoop, const hash_digest& secret);

    ec_private ours_;
    ec_public theirs_;
};

#endif
