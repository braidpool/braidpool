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

#include "share.hpp"
#include <boost/test/unit_test.hpp>

using namespace bp;

BOOST_AUTO_TEST_SUITE(pool_tests)

BOOST_AUTO_TEST_CASE(share_test__constructor__returns_share)
{
    hash_digest work_hash = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    hash_digest merkle_root = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26g");
    bp::share instance(std::move(work_hash), 100, 200, std::move(merkle_root),
        1, data_chunk { 21u }, data_chunk { 22u }, data_chunk { 23u }, {});
    BOOST_CHECK(instance.work_hash() == work_hash);
}

BOOST_AUTO_TEST_CASE(share_test__serialization__should_deserialize)
{
    hash_digest work_hash = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    hash_digest merkle_root = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26e");
    hash_digest share1 = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26d");
    hash_list shares { share1 };
    bp::share instance(std::move(work_hash), 100, 200, std::move(merkle_root),
        1, data_chunk { 21u }, data_chunk { 22u }, data_chunk { 23u },
        std::move(shares));

    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, instance);

    msgpack::object_handle oh = msgpack::unpack(sbuf.data(), sbuf.size());
    msgpack::object obj = oh.get();

    bp::share deserialized_share;
    obj.convert(deserialized_share);

    BOOST_CHECK(deserialized_share.work_hash() == work_hash);
    BOOST_CHECK(deserialized_share.nonce() == 100);
    BOOST_CHECK(deserialized_share.extra_nonce() == 200);
    BOOST_CHECK(deserialized_share.merkle_root() == merkle_root);
    BOOST_CHECK(deserialized_share.timestamp() == 1);
    BOOST_CHECK(deserialized_share.hub_pubkey() == data_chunk { 21u });
    BOOST_CHECK(deserialized_share.miner_pubkey() == data_chunk { 22u });
    BOOST_CHECK(deserialized_share.tor_service_pubkey() == data_chunk { 23u });
    BOOST_CHECK(deserialized_share.shares().size() == 1);
    BOOST_CHECK(deserialized_share.shares()[0] == share1);
}

BOOST_AUTO_TEST_SUITE_END()
