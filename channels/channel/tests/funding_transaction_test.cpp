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
#include <boost/test/unit_test.hpp>

using namespace one_way_channel;

#define TX1                                                                    \
    "0100000001f08e44a96bfb5ae63eda1a6620adae37ee37ee4777fb0336e1bbbc"         \
    "4de65310fc010000006a473044022050d8368cacf9bf1b8fb1f7cfd9aff63294"         \
    "789eb1760139e7ef41f083726dadc4022067796354aba8f2e02363c5e510aa7e"         \
    "2830b115472fb31de67d16972867f13945012103e589480b2f746381fca01a9b"         \
    "12c517b7a482a203c8b2742985da0ac72cc078f2ffffffff02f0c9c467000000"         \
    "001976a914d9d78e26df4e4601cf9b26d09c7b280ee764469f88ac80c4600f00"         \
    "0000001976a9141ee32412020a324b93b1a1acfdfff6ab9ca8fac288ac000000"         \
    "00"

#define TX1_HASH                                                               \
    "bf7c3f5a69a78edd81f3eff7e93a37fb2d7da394d48db4d85e7e5353b9b8e270"

#define SCRIPT_2_OF_2_MULTISIG                                                 \
    "2 [03dcfd9e580de35d8c2060d76dbf9e5561fe20febd2e64380e860a4d59f15ac864] "  \
    "[02440e0304bf8d32b2012994393c6a477acf238dd6adb4c3cef5bfa72f30c9861c] 2 "  \
    "checkmultisig"

BOOST_AUTO_TEST_SUITE(funding_transction_tests)

BOOST_AUTO_TEST_CASE(fund_transction__valid_inputs__returns_valid_transaction)
{
    data_chunk hub, miner, hub_noncoop, miner_noncoop;
    decode_base16(hub,
        "02100a1a9ca2c18932d6577c58f225580184d0e08226d41959874ac963e3c1b2fe");
    decode_base16(miner,
        "0275983913e60093b767e85597ca9397fb2f418e57f998d6afbbc536116085b1cb");
    decode_base16(hub_noncoop,
        "02100a1a9ca2c18932d6577c58f225580184d0e08226d41959874ac963e3c1b2ff");
    decode_base16(miner_noncoop,
        "0275983913e60093b767e85597ca9397fb2f418e57f998d6afbbc536116085b1cc");
    hash_digest secret = hash_literal(
        "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b");

    hash_digest tx1_hash_digest = hash_literal(TX1_HASH);

    funding_transaction instance(tx1_hash_digest, 0, SCRIPT_2_OF_2_MULTISIG,
        hub, miner, hub_noncoop, miner_noncoop, secret, 1000);

    BOOST_CHECK(instance.get_transaction().inputs().size() == 1);
    auto input = instance.get_transaction().inputs().front();
    output_point prev_out { tx1_hash_digest, 0 };
    BOOST_CHECK(input.previous_output() == prev_out);
    const auto& input_ops = input.script().operations();
    BOOST_REQUIRE_EQUAL(input_ops.size(), 5u);
    BOOST_CHECK(input.sequence() == 0xffffffff);

    BOOST_CHECK(instance.get_transaction().outputs().size() == 1);
    const auto tx_output = instance.get_transaction().outputs().front();
    BOOST_CHECK(tx_output.value() == 1000);
    const auto tx_output_script = tx_output.script();
    const auto output_ops = tx_output_script.operations();
    BOOST_CHECK_EQUAL(output_ops.size(), 13u);
    BOOST_CHECK(output_ops[0] == opcode::if_);
    BOOST_CHECK(output_ops[1] == opcode::push_positive_2);
    BOOST_CHECK(output_ops[2] == to_chunk(wallet::ec_public { hub }.point()));
    BOOST_CHECK(output_ops[3] == to_chunk(wallet::ec_public { miner }.point()));
    BOOST_CHECK(output_ops[4] == opcode::push_positive_2);
    BOOST_CHECK(output_ops[5] == opcode::else_);
    BOOST_CHECK(output_ops[6] == opcode::push_positive_2);
    BOOST_CHECK(
        output_ops[7] == to_chunk(wallet::ec_public { hub_noncoop }.point()));
    BOOST_CHECK(
        output_ops[8] == to_chunk(wallet::ec_public { miner_noncoop }.point()));
    BOOST_CHECK(output_ops[9] == opcode::push_positive_2);
    BOOST_CHECK(output_ops[10] == to_chunk(secret));
    BOOST_CHECK(output_ops[11] == opcode::equalverify);
    BOOST_CHECK(output_ops[12] == opcode::endif);
}

BOOST_AUTO_TEST_SUITE_END()
