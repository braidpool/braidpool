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

#include "refund_transaction.hpp"

#include <string>

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

refund_transaction::refund_transaction(
    const transaction& fund_transaction, const payment_address hub_address)
    : transaction_()
{
    // TODO: Implement
}

}
