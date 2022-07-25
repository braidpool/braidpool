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

#include "funding_transaction.hpp"
#include "bitcoin/system/chain/transaction.hpp"

#include <string>

namespace one_way_channel {

using namespace libbitcoin::system;
using namespace libbitcoin::system::chain;
using namespace libbitcoin::system::machine;
using namespace libbitcoin::system::wallet;

operations funding_transaction::make_fund_output(const ec_public& hub,
    const ec_public& miner, const ec_public& hub_noncoop,
    const ec_public& miner_noncoop, const hash_digest& secret)
{
    operations ops;
    // length of [if 2 H M 2 else 2 H' M' 2 secret equalverify
    // endif] = 13
    ops.reserve(13);

    ops.emplace_back(opcode::if_);

    // 2 of 2 H M
    this->push_2of2_multisig(ops, hub, miner);

    ops.emplace_back(opcode::else_);

    // 2 of 2 H' M'
    this->push_2of2_multisig(ops, hub_noncoop, miner_noncoop);

    // secret equalverify
    ops.emplace_back(operation(to_chunk(secret), true));
    ops.emplace_back(opcode::equalverify);

    ops.emplace_back(opcode::endif);
    return ops;
}

funding_transaction::funding_transaction(const hash_digest& input_tx_hash,
    const uint32_t input_index, const std::string& script_sig,
    const ec_public& hub, const ec_public& miner, const ec_public& hub_noncoop,
    const ec_public& miner_noncoop, const hash_digest& secret, uint64_t value)
{
    // input from input_tx_hash, input_index and script_sig
    point prevout_point { input_tx_hash, input_index };
    script input_script(script_sig);
    input tx_input { prevout_point, input_script, 0xffffffff };

    // outputs with 2of2 multisig and hashlock
    const auto ops = this->make_fund_output(
        hub, miner, hub_noncoop, miner_noncoop, secret);
    const script output_script { ops };
    const output tx_output { value, ops };

    this->transaction_
        = std::move(transaction(2u, { tx_input }, { tx_output }, 0u));
}
}
