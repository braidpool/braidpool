cmake_minimum_required(VERSION 3.10)

# set the project name
project(pool VERSION 1.0)

find_package(PkgConfig REQUIRED)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)

configure_file(pool_config.h.in pool_config.h)

pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

enable_testing()

find_package(Boost 1.76 REQUIRED COMPONENTS system filesystem unit_test_framework REQUIRED)

list(APPEND EXTRA_INCLUDES "${PROJECT_SOURCE_DIR}/include")

list(APPEND EXTRA_LIBS ${LIBBITCOIN-SYSTEM_LINK_LIBRARIES})
list(APPEND EXTRA_INCLUDES ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})


# add the executable
add_executable(bp
  src/pool.cpp
  src/share.cpp
  src/work.cpp
  src/p2p/node.cpp
  src/p2p/connection.cpp)

target_link_libraries(bp PUBLIC ${EXTRA_LIBS})

target_include_directories(bp PUBLIC
  "${PROJECT_BINARY_DIR}"
  ${EXTRA_INCLUDES}
  )


install(TARGETS bp DESTINATION bin)

# Add tests
add_executable(pool_test
  src/share.cpp
  src/work.cpp
  src/p2p/node.cpp
  src/p2p/connection.cpp
  ${PROJECT_SOURCE_DIR}/tests/main.cpp
  ${PROJECT_SOURCE_DIR}/tests/share_test.cpp
  ${PROJECT_SOURCE_DIR}/tests/work_test.cpp
  )

target_link_libraries(pool_test PUBLIC
  ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
  ${EXTRA_LIBS}
  )

target_include_directories(pool_test PUBLIC
  "${PROJECT_BINARY_DIR}"
  ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
  ${EXTRA_INCLUDES}
  )

add_test(NAME pool_test
  COMMAND ./pool_test)
