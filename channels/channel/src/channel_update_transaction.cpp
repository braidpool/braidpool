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

#include "channel_update_transaction.hpp"

#include <string>

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

channel_update_transaction::channel_update_transaction(
    const transaction& fund_transaction, const ec_public& hub,
    const ec_public& miner, const ec_public& hub_noncoop,
    const ec_public& miner_noncoop, const hash_digest& secret)
    : channel_transaction()
{
    // TODO: Implement
}
}
