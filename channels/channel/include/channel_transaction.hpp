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

#ifndef CHANNEL_TRANSACTION_HPP
#define CHANNEL_TRANSACTION_HPP

#include <string.h>

#include <bitcoin/system.hpp>

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

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
