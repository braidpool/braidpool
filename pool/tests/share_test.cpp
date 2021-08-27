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
    const hash_digest work_hash = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    const hash_digest merkle_root = hash_literal(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26g");
    bp::share instance(work_hash, 100, 200, merkle_root, 1, data_chunk { 21u },
        data_chunk { 22u }, data_chunk { 23u }, {});
    BOOST_CHECK(instance.work_hash() == work_hash);
}

BOOST_AUTO_TEST_SUITE_END()
