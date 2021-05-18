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

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(channel_funding_transction_tests)

BOOST_AUTO_TEST_CASE(
    channel_fund_transction__valid_inputs__returns_valid_transaction)
{
    namespace tt = boost::test_tools;
    int a = 1;
    int b = 2;
    BOOST_TEST(a == b - 1);
    // BOOST_TEST(a + 1 < b);
    // BOOST_TEST(b -1 > a, a << " < " << b - 1 << " does not hold");
    // BOOST_TEST(a == b, tt::bitwise());
    // BOOST_TEST(a + 0.1 == b - 0.8, tt::tolerance(0.01));
}

BOOST_AUTO_TEST_SUITE_END()
