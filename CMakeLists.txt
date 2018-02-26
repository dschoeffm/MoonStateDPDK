cmake_minimum_required(VERSION 2.8)
project(MoonStateDPDK CXX)

set(CMAKE_CXX_FLAGS "-fno-stack-protector -Wall -Wextra -Wno-unused-parameter -g -O3 -std=gnu++11 -march=native -msse4.2")
set(CMAKE_C_FLAGS "-fno-stack-protector -Wall -Wextra -Wno-unused-parameter -g -O3 -std=gnu11 -march=native -msse4.2")
set(CMAKE_EXE_LINKER_FLAGS "-rdynamic")

add_subdirectory(deps)


include_directories(
	${CMAKE_CURRENT_SOURCE_DIR}/src
	${CMAKE_CURRENT_SOURCE_DIR}/deps/dpdk/x86_64-native-linuxapp-gcc/include
	${CMAKE_CURRENT_SOURCE_DIR}/deps/MoonState/include/
)

set(files
	src/main
)

set(libraries
	-Wl,--whole-archive
	MoonState
)

link_directories(
	${CMAKE_CURRENT_SOURCE_DIR}/deps/dpdk/x86_64-native-linuxapp-gcc/lib
	${CMAKE_CURRENT_SOURCE_DIR}/deps/MoonState/deps/openssl/
	${CMAKE_CURRENT_SOURCE_DIR}/deps/MoonState/deps/AstraeusVPN/deps/libsodium_install/lib
	${CMAKE_CURRENT_SOURCE_DIR}/deps/MoonState/deps/tbb/
)

add_executable(MoonStateDPDK ${files})
target_link_libraries(MoonStateDPDK ${libraries})

add_dependencies(MoonStateDPDK DPDK)
