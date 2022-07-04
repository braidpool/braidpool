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

#ifndef BP_NODE_HPP
#define BP_NODE_HPP

#include <boost/core/noncopyable.hpp>
#include <memory>
#include <p2p/define.hpp>

#include "p2p/connection.hpp"
#include "p2p/connections_manager.hpp"
#include "p2p/protocol.hpp"
#include "runner.hpp"

namespace bp {
namespace p2p {
template <typename connection_t>
class node : private boost::noncopyable {
 public:
  using connection_ptr = std::shared_ptr<connection_t>;
  using connections_mgr = connections_manager<connection_ptr>;
  using shares_protocol = protocol<connection_ptr>;

  node(io_context& ctx, const std::string& listen_address,
       const std::string& listen_port, connections_mgr& manager);
  ~node();
  void start();
  void stop();
  awaitable<void> connect_to_peers(const std::string& host,
                                   const std::string& port);

 private:
  awaitable<void> listen(tcp::acceptor& acceptor);

  std::unique_ptr<tcp::acceptor> acceptor_;

  io_context& ctx_;

  connections_mgr& connections_mgr_;
};

}  // namespace p2p
}  // namespace bp

#include "impl/p2p/node.ipp"

#endif
