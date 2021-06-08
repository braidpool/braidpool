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

#ifndef CHANNEL_TRANSACTION_HPP
#define CHANNEL_TRANSACTION_HPP

#include <string.h>

#include <bitcoin/system.hpp>
#include <bitcoin/system/machine/rule_fork.hpp>

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

// Use the same fork rules that are enabled by default in libbitcoin-node
constexpr uint32_t active_forks = rule_fork::bip16_rule | rule_fork::bip30_rule
    | rule_fork::bip34_rule | rule_fork::bip66_rule | rule_fork::bip65_rule
    | rule_fork::bip90_rule | rule_fork::bip68_rule | rule_fork::bip112_rule
    | rule_fork::bip113_rule | rule_fork::bip141_rule | rule_fork::bip143_rule
    | rule_fork::bip147_rule;

// Abstract super class for all transaction classes
class channel_transaction {
public:
    channel_transaction();

    // data_chunk to_data() const { return transaction_.to_data(false, false);
    // };

    // virtual void add_endorsement(ec_private& key) = 0;

    transaction get_transaction() const;

protected:
    transaction transaction_;

    void push_2of2_multisig(
        operation::list& ops, const ec_public& key_1, const ec_public& key_2);
};
}

#endif
