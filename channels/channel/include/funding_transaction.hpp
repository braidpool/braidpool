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

#ifndef FUNDING_TRANSACTION_HPP
#define FUNDING_TRANSACTION_HPP

#include "channel_transaction.hpp"
#include <string.h>

namespace one_way_channel {

using namespace bc;
using namespace bc::chain;
using namespace bc::machine;
using namespace bc::wallet;

// Funding transaction for one way channel management.
class funding_transaction : public channel_transaction {
public:
    // Create a funding transaction given the input points, hub's and
    // miner's co-operative and not co-operative public keys, as well
    // as the hash of the preimage
    // output: if 1 (2 of 2 H and M) else (2 of 2 H' and M' and secret
    // equalverify)
    funding_transaction(const hash_digest& input_tx_hash,
        const uint32_t input_index, const std::string& script_sig,
        const ec_public& hub, const ec_public& miner,
        const ec_public& hub_noncoop, const ec_public& miner_noncoop,
        const hash_digest& secret, uint64_t value);

private:
    operation::list make_fund_output(const ec_public& hub,
        const ec_public& miner, const ec_public& hub_noncoop,
        const ec_public& miner_noncoop, const hash_digest& secret);
};
}

#endif
