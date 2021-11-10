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

#include "work.hpp"
#include <boost/test/unit_test.hpp>
#include <msgpack.hpp>

using namespace bp;

BOOST_AUTO_TEST_SUITE(pool_tests)

BOOST_AUTO_TEST_CASE(work_test__constructor__returns_work)
{
    hash_digest previous_block = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    bp::work instance(
        10, std::move(previous_block), 1000000000, "some_coinbase", {});
    BOOST_CHECK(instance.version() == 10);
}

BOOST_AUTO_TEST_CASE(work_test__serialization__should_deserialize)
{
    hash_digest previous_block = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    bp::work instance(
        10, std::move(previous_block), 1000000000, "some_coinbase", {});

    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, instance);

    msgpack::object_handle oh = msgpack::unpack(sbuf.data(), sbuf.size());
    msgpack::object obj = oh.get();

    bp::work deserialized_work;
    obj.convert(deserialized_work);

    BOOST_CHECK(deserialized_work.version() == 10);
    BOOST_CHECK(deserialized_work.previous_block_hash() == previous_block);
    BOOST_CHECK(deserialized_work.difficulty() == 1000000000);
    BOOST_CHECK(deserialized_work.coinbase() == "some_coinbase");
}

BOOST_AUTO_TEST_SUITE_END()
