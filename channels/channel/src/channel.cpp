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

#include "channel.hpp"

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

script
one_way_channel::make_cooperative_output(const ec_public& key_1, const ec_public& key_2)
{
    point_list keys{key_1.point(), key_2.point()};
    auto result_script = script();
    result_script.from_operations(script::to_pay_multisig_pattern(2u, keys));
    return result_script;
}

script
one_way_channel::make_non_cooperative_output(const ec_public& key_1, const ec_public& key_2, const hash_digest& secret)
{
    point_list keys{key_1.point(), key_2.point()};
    auto ops = script::to_pay_multisig_pattern(2u, keys);

    // this will make ops grow more than reserved in to_pay_multisig_pattern
    ops.emplace_back(to_chunk(secret));
    ops.emplace_back(opcode::equalverify);

    auto result_script = script();
    result_script.from_operations(ops);
    return result_script;
}

transaction
one_way_channel::fund_transaction(const hash_digest& input_tx_hash,
        const uint32_t input_index, const ec_public& hub, const ec_public& miner,
    const ec_public& hub_noncoop, const ec_public& miner_noncoop, const hash_digest& secret, uint64_t value)
{
    // input from input_tx_hash and input_index
    auto prev_out = output_point{input_tx_hash, input_index};

    // output 1: 2 of 2 multisig for hub and miner for value coins
    auto script_cooperative = this->make_cooperative_output(hub.point(), miner.point());
    auto output_1 = output{value, script_cooperative};

    // output 2: 2 of 2 multisig for hub' and miner' for value coins
    // auto script_non_cooperative = this->make_2of2_multisig(hub_noncoop.point(), miner_noncoop.point());
    // auto output_2 = output{value, script_non_cooperative};

    // sign prev_out
    // sign for H' of the output 2
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

