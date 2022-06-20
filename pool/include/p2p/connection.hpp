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

#ifndef BP_CONNECTION_HPP
#define BP_CONNECTION_HPP

#include <boost/asio/awaitable.hpp>
#include <boost/core/noncopyable.hpp>
#include <memory>
#include <p2p/define.hpp>

using boost::asio::awaitable;

namespace bp {
namespace p2p {
class connection : private boost::noncopyable {
 public:
  typedef std::shared_ptr<connection> connection_ptr;
  connection(tcp::socket&& sock);
  ~connection();
  void start_receive_from_peer();
  awaitable<void> send_to_peer(std::string message);
  socket& get_socket() { return socket_; }

 private:
  awaitable<void> receive_from_peer();

 private:
  tcp::socket socket_;
};
}  // namespace p2p
}  // namespace bp

#endif
