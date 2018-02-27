cmake_minimum_required(VERSION 2.8)
project(MoonStateDPDK CXX)

set(CMAKE_CXX_FLAGS "-fno-stack-protector -Wall -Wextra -Wno-unused-parameter -g -O3 -std=gnu++11 -march=native -msse4.2")
set(CMAKE_C_FLAGS "-fno-stack-protector -Wall -Wextra -Wno-unused-parameter -g -O3 -std=gnu11 -march=native -msse4.2")
set(CMAKE_EXE_LINKER_FLAGS "-rdynamic")

set(DPDK_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/deps/dpdk/x86_64-native-linuxapp-gcc/include")
set(DPDK_LIB_DIR "${CMAKE_CURRENT_SOURCE_DIR}/deps/dpdk/x86_64-native-linuxapp-gcc/lib")

add_subdirectory(deps)

include_directories(
	${CMAKE_CURRENT_SOURCE_DIR}/src
	${CMAKE_CURRENT_SOURCE_DIR}/deps/dpdk/x86_64-native-linuxapp-gcc/include
	${CMAKE_CURRENT_SOURCE_DIR}/deps/MoonState/include/
)

SET(DPDK_LIBS
	rte_net	     rte_ethdev       rte_distributor 	 rte_kni       rte_mbuf       	  rte_pmd_bond         rte_pmd_ring  	rte_power
	rte_acl      rte_eal          rte_kvargs   	 rte_mempool   rte_mempool_ring	  rte_pmd_e1000        rte_pmd_virtio   rte_ring
	rte_cfgfile  rte_hash         rte_lpm      	 rte_meter     rte_pmd_i40e   	  rte_pmd_vmxnet3_uio  rte_sched        rte_timer
	rte_cmdline  rte_ip_frag      rte_pipeline 	 rte_pmd_ixgbe rte_mempool_stack  rte_port             rte_table        rte_pmd_bnxt
	rte_pmd_ena  rte_pmd_nfp
)

set(files
	src/main
)

set(libraries
	-Wl,--whole-archive
	MoonState
	-Wl,--start-group ${DPDK_LIBS} numa -Wl,--end-group
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
