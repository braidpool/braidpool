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

#ifndef P2P_DEFINE_HPP
#define P2P_DEFINE_HPP

#include <atomic>
#include <boost/asio.hpp>

namespace bp {
namespace p2p {

    using error_code = boost::system::error_code;
    using io_service = boost::asio::io_service;
    using io_context = boost::asio::io_context;
    using tcp = boost::asio::ip::tcp;
    using tcp_acceptor = tcp::acceptor;
    using endpoint = tcp::endpoint;
    using socket = tcp::socket;
    using socket_ptr = std::shared_ptr<socket>;
    using ipv4 = boost::asio::ip::address_v4;
}
}

#endif
