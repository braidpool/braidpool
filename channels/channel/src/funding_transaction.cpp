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

#include "funding_transaction.hpp"

#include <string>

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

void funding_transaction::push_2of2_multisig(
    operation::list& ops, const ec_public& key_1, const ec_public& key_2)
{
    ops.emplace_back(opcode::push_positive_2);
    ops.emplace_back(to_chunk(key_1.point()));
    ops.emplace_back(to_chunk(key_2.point()));
    ops.emplace_back(opcode::push_positive_2);
}

operation::list funding_transaction::make_fund_output(const ec_public& hub,
    const ec_public& miner, const ec_public& hub_noncoop,
    const ec_public& miner_noncoop, const hash_digest& secret)
{
    operation::list ops;
    // length of [if 2 H M 2 else 2 H' M' 2 secret equalverify endif] = 13
    ops.reserve(13);

    ops.emplace_back(opcode::if_);

    // 2 of 2 H M
    this->push_2of2_multisig(ops, hub, miner);

    ops.emplace_back(opcode::else_);

    // 2 of 2 H' M'
    this->push_2of2_multisig(ops, hub_noncoop, miner_noncoop);

    // secret equalverify
    ops.emplace_back(to_chunk(secret));
    ops.emplace_back(opcode::equalverify);

    ops.emplace_back(opcode::endif);
    return ops;
}

transaction funding_transaction::fund_transaction(
    const hash_digest& input_tx_hash, const uint32_t input_index,
    const std::string& script_sig, const ec_public& hub, const ec_public& miner,
    const ec_public& hub_noncoop, const ec_public& miner_noncoop,
    const hash_digest& secret, uint64_t value)
{
    // input from input_tx_hash, input_index and script_sig
    auto prev_out = output_point { input_tx_hash, input_index };
    data_chunk script_sig_bytes;
    decode_base16(script_sig_bytes, script_sig);
    script input_script;
    input_script.from_data(to_chunk(script_sig_bytes), false);
    input tx_input { prev_out, input_script, 0xffffffff };

    // outputs with 2of2 multisig and hashlock
    const auto ops = this->make_fund_output(
        hub, miner, hub_noncoop, miner_noncoop, secret);
    const script output_script { ops };
    const output tx_output { value, ops };

    auto tx = transaction();
    tx.inputs().push_back(tx_input);
    tx.outputs().push_back(tx_output);

    return tx;
}

transaction funding_transaction::refund_transaction(
    const transaction& fund_transaction, const payment_address hub_address)
{
    // TODO: Implement
    return transaction {};
}

transaction funding_transaction::channel_update_transaction(
    const transaction& fund_transaction, const ec_public& hub,
    const ec_public& miner, const ec_public& hub_noncoop,
    const ec_public& miner_noncoop, const hash_digest& secret)
{
    // TODO: Implement
    return transaction {};
}
}
