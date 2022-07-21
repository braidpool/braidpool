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
#include <boost/asio/executor.hpp>
#include <boost/asio/io_context.hpp>
#include <boost/core/noncopyable.hpp>
#include <boost/enable_shared_from_this.hpp>
#include <memory>
#include <p2p/define.hpp>

#include "p2p/connections_manager.hpp"
#include "p2p/protocol.hpp"

using boost::asio::awaitable;

namespace bp {
namespace p2p {

class connection_iface {
 public:
  // connection_iface(tcp::socket&& sock);
  virtual ~connection_iface(){};
  virtual void start() = 0;
  virtual awaitable<void> send_to_peer(std::string message) = 0;
  virtual void shutdown() = 0;
  virtual socket& get_socket() = 0;
};

class connection : private boost::noncopyable,
                   public connection_iface,
                   public boost::enable_shared_from_this<connection> {
 public:
  connection(tcp::socket&& sock);
  virtual ~connection();
  virtual void start() override;
  awaitable<void> send_to_peer(std::string message) override;

  void shutdown() override;

  socket& get_socket() override { return socket_; }

 protected:
  tcp::socket socket_;

 private:
  awaitable<void> receive_from_peer();
};
}  // namespace p2p
}  // namespace bp

#endif
