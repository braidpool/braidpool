cmake_minimum_required(VERSION 3.10)

# set the project name
project(pool VERSION 1.0)

find_package(PkgConfig REQUIRED)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)

include(FetchContent)
FetchContent_Declare(
  googletest
  URL https://github.com/google/googletest/archive/609281088cfefc76f9d0ce82e1ff6c30cc3591e5.zip
  )
FetchContent_MakeAvailable(googletest)

configure_file(pool_config.h.in pool_config.h)

pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

enable_testing()

find_package(Boost 1.76 REQUIRED COMPONENTS system filesystem log_setup REQUIRED)

list(APPEND EXTRA_INCLUDES "${PROJECT_SOURCE_DIR}/include")

list(APPEND EXTRA_LIBS ${LIBBITCOIN-SYSTEM_LINK_LIBRARIES})
list(APPEND EXTRA_INCLUDES ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})

find_package(msgpack REQUIRED)
add_definitions(-DMSGPACK_USE_BOOST)

# add the executable
add_executable(bp
  src/pool.cpp
  src/share.cpp
  src/work.cpp
  src/p2p/node.cpp
  src/p2p/connection.cpp)

target_link_libraries(bp PUBLIC
  ${Boost_LOG_SETUP_LIBRARY}
  msgpackc-cxx
  ${EXTRA_LIBS}
  )

target_include_directories(bp PUBLIC
  "${PROJECT_BINARY_DIR}"
  ${Boost_LOG_SETUP_LIBRARY}
  msgpackc-cxx
  ${EXTRA_INCLUDES}
  )


install(TARGETS bp DESTINATION bin)

# Add tests
add_executable(pool_test
  src/share.cpp
  src/work.cpp
  src/p2p/node.cpp
  src/p2p/connection.cpp
  ${PROJECT_SOURCE_DIR}/tests/share_test.cpp
  ${PROJECT_SOURCE_DIR}/tests/work_test.cpp
  )

target_link_libraries(pool_test PUBLIC
  ${Boost_LOG_SETUP_LIBRARY}
  gtest_main
  msgpackc-cxx
  ${EXTRA_LIBS}
  )

target_include_directories(pool_test PUBLIC
  "${PROJECT_BINARY_DIR}"
  ${Boost_LOG_SETUP_LIBRARY}
  msgpackc-cxx
  ${EXTRA_INCLUDES}
  )

include(GoogleTest)
gtest_discover_tests(pool_test)

add_test(NAME pool_test
  COMMAND ./pool_test)
