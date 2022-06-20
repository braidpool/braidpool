cmake_minimum_required(VERSION 3.10)

# set the project name
project(pool VERSION 1.0)

find_package(PkgConfig REQUIRED)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)

# Generate compile_commands.json for flycheck/lsp support
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include(FetchContent)
FetchContent_Declare(
  googletest
  URL https://github.com/google/googletest/archive/609281088cfefc76f9d0ce82e1ff6c30cc3591e5.zip
  )
FetchContent_MakeAvailable(googletest)

configure_file(pool_config.h.in pool_config.h)

pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

enable_testing()

find_package(Boost 1.76 REQUIRED COMPONENTS system filesystem thread log log_setup)

list(APPEND EXTRA_INCLUDES "${PROJECT_SOURCE_DIR}/include")

list(APPEND EXTRA_LIBS ${LIBBITCOIN-SYSTEM_LINK_LIBRARIES})
list(APPEND EXTRA_INCLUDES ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})

find_package(msgpack REQUIRED)
add_definitions(-DMSGPACK_USE_BOOST)

add_executable(bp
  src/runner.cpp
  src/pool.cpp
  src/share.cpp
  src/work.cpp
  src/p2p/node.cpp
  src/p2p/connection.cpp
  src/p2p/protocol.cpp)

target_link_libraries(bp PUBLIC
  ${Boost_LIBRARIES}
  Boost::log Boost::log_setup
  msgpackc-cxx
  ${EXTRA_LIBS}
  )

target_include_directories(bp PUBLIC
  "${PROJECT_BINARY_DIR}"
  ${Boost_LIBRARIES}
  msgpackc-cxx
  ${EXTRA_INCLUDES}
  )


install(TARGETS bp DESTINATION bin)

# Add tests
add_executable(pool_test
  src/runner.cpp
  src/share.cpp
  src/work.cpp
  src/p2p/node.cpp
  src/p2p/connection.cpp
  src/p2p/protocol.cpp
  ${PROJECT_SOURCE_DIR}/test/share_test.cpp
  ${PROJECT_SOURCE_DIR}/test/work_test.cpp
  ${PROJECT_SOURCE_DIR}/test/p2p/node_test.cpp
  )

target_link_libraries(pool_test PUBLIC
  ${Boost_LIBRARIES}
  Boost::log Boost::log_setup
  gtest_main
  msgpackc-cxx
  ${EXTRA_LIBS}
  )

target_include_directories(pool_test PUBLIC
  "${PROJECT_BINARY_DIR}"
  msgpackc-cxx
  ${EXTRA_INCLUDES}
  )

include(GoogleTest)
gtest_discover_tests(pool_test)

add_test(NAME pool_test
  COMMAND ./pool_test)
