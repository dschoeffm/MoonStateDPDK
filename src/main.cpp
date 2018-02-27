/*-
 *   BSD LICENSE
 *
 *   Copyright(c) 2010-2016 Intel Corporation. All rights reserved.
 *   All rights reserved.
 *
 *   Redistribution and use in source and binary forms, with or without
 *   modification, are permitted provided that the following conditions
 *   are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in
 *       the documentation and/or other materials provided with the
 *       distribution.
 *     * Neither the name of Intel Corporation nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 *   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <inttypes.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/queue.h>
#include <sys/types.h>

#include <rte_atomic.h>
#include <rte_branch_prediction.h>
#include <rte_common.h>
#include <rte_cycles.h>
#include <rte_debug.h>
#include <rte_eal.h>
#include <rte_ethdev.h>
#include <rte_ether.h>
#include <rte_interrupts.h>
#include <rte_launch.h>
#include <rte_lcore.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_mbuf.h>
#include <rte_memcpy.h>
#include <rte_memory.h>
#include <rte_mempool.h>
#include <rte_memzone.h>
#include <rte_pci.h>
#include <rte_per_lcore.h>
#include <rte_prefetch.h>
#include <rte_random.h>

#include <string>

#include "IPv4_5TupleL2Ident.hpp"
#include "astraeusClient.hpp"
#include "cryptoProto.hpp"
#include "mbuf.hpp"
#include "stateMachine.hpp"

using SM = StateMachine<IPv4_5TupleL2Ident<mbuf>, mbuf>;

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 1;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define NB_MBUF 8192

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 128
#define RTE_TEST_TX_DESC_DEFAULT 512
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

/* mask of enabled ports */
static uint16_t portId;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

// static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

struct rte_eth_conf port_conf;
struct rte_mempool *pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;
struct port_statistics port_statistics;

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 1; /* default period is 1 second */

static struct ether_addr srcMac;
static struct ether_addr dstMac;

static uint32_t dstIP = 0xc0a80002;
static uint32_t srcIP = 0xc0a80003;

/* Print out statistics on packets dropped */
static void print_stats(void) {
	uint64_t total_packets_dropped, total_packets_tx, total_packets_rx;

	total_packets_dropped = 0;
	total_packets_tx = 0;
	total_packets_rx = 0;

	static int calledTimes = 1;

	// const char clr[] = {27, '[', '2', 'J', '\0'};
	// const char topLeft[] = {27, '[', '1', ';', '1', 'H', '\0'};

	/* Clear screen and move to top left */
	// printf("%s%s", clr, topLeft);

	printf("\nPort statistics ====================================");

	printf("\nStatistics for port %u ------------------------------"
		   "\nPackets sent: %24" PRIu64 "\nPackets received: %20" PRIu64
		   "\nPackets dropped: %21" PRIu64,
		portId, port_statistics.tx, port_statistics.rx, port_statistics.dropped);

	total_packets_dropped += port_statistics.dropped;
	total_packets_tx += port_statistics.tx;
	total_packets_rx += port_statistics.rx;

	printf("\nAggregate statistics ==============================="
		   "\nTotal packets sent: %18" PRIu64 "\nMillion packets sent per second: %18" PRIu64
		   "\nTotal packets received: %14" PRIu64 "\nTotal packets dropped: %15" PRIu64,
		total_packets_tx, ((total_packets_tx / 1000000) / (calledTimes++)), total_packets_rx,
		total_packets_dropped);
	printf("\n====================================================\n");
}

static void mac_update(struct rte_mbuf *m) {
	struct ether_hdr *eth;

	eth = rte_pktmbuf_mtod(m, struct ether_hdr *);

	/* src addr */
	ether_addr_copy(&srcMac, &eth->s_addr);
}

static void simple_forward(struct rte_mbuf *m) {

	mac_update(m);

	/*
		int sent = rte_eth_tx_burst(portId, 0, &m, 1);
		if (sent)
			port_statistics.tx += sent;
	*/
}

/* main processing loop */
static void main_loop(void) {
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	unsigned lcore_id;
	unsigned nb_rx;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;

	prev_tsc = 0;
	timer_tsc = 0;

	lcore_id = rte_lcore_id();

	RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

	while (!force_quit) {
		cur_tsc = rte_rdtsc();
		diff_tsc = cur_tsc - prev_tsc;

		/* if timer is enabled */
		if (timer_period > 0) {

			/* advance the timer */
			timer_tsc += diff_tsc;

			/* if timer has reached its timeout */
			if (unlikely(timer_tsc >= timer_period)) {

				/* do this only on master core */
				// only one core...
				// if (lcore_id == rte_get_master_lcore()) {
				print_stats();
				/* reset the timer */
				timer_tsc = 0;
				//}
			}
		}

		prev_tsc = cur_tsc;

		nb_rx = rte_eth_rx_burst((uint8_t)portId, 0, pkts_burst, MAX_PKT_BURST);

		port_statistics.rx += nb_rx;

		for (unsigned int j = 0; j < nb_rx; j++) {
			m = pkts_burst[j];
			rte_prefetch0(rte_pktmbuf_mtod(m, void *));
			simple_forward(m);
		}

		if (nb_rx > 0) {
			int sent = rte_eth_tx_burst(portId, 0, pkts_burst, nb_rx);
			if (sent) {
				port_statistics.tx += sent;
			}
		}
	}
}

static AstraeusProto::identityHandle ident;

static void prepareAstraeusInit(struct rte_mbuf *pkt, uint32_t srcIP, uint32_t dstIP,
	uint16_t srcPort, uint16_t dstPort /*, SM &sm*/) {

	IPv4_5TupleL2Ident<mbuf>::ConnectionID cID;
	cID.dstIP = htonl(srcIP);
	cID.srcIP = htonl(dstIP);
	cID.dstPort = htons(srcPort);
	cID.srcPort = htons(dstPort);
	cID.proto = Headers::IPv4::PROTO_UDP;

	auto state = Astraeus_Client::createStateData(&ident, srcIP, dstIP, srcPort, dstPort);
	Astraeus_Client::initHandshakeNoTransition(state, static_cast<mbuf *>(pkt));
	state.state = Astraeus_Client::States::HANDSHAKE;

	// sm.addStateNoFun(cID, state);
}

static void main_loop_astraeus(void) {
	struct rte_mbuf *pkts_burst[64];
	unsigned int burstSize = 64;
	struct rte_mbuf *m;
	unsigned lcore_id;
	// unsigned nb_rx;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;

	// SM sm;
	// Astraeus_Client::configStateMachine(sm, nullptr);

	AstraeusProto::generateIdentity(ident);

	prev_tsc = 0;
	timer_tsc = 0;

	lcore_id = rte_lcore_id();

	RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

	while (!force_quit) {
		cur_tsc = rte_rdtsc();
		diff_tsc = cur_tsc - prev_tsc;

		/* if timer is enabled */
		if (timer_period > 0) {

			/* advance the timer */
			timer_tsc += diff_tsc;

			/* if timer has reached its timeout */
			if (unlikely(timer_tsc >= timer_period)) {

				/* do this only on master core */
				// only one core...
				// if (lcore_id == rte_get_master_lcore()) {
				print_stats();
				/* reset the timer */
				timer_tsc = 0;
				//}
			}
		}

		prev_tsc = cur_tsc;

		// nb_rx = rte_eth_rx_burst((uint8_t)portId, 0, pkts_burst, MAX_PKT_BURST);
		// port_statistics.rx += nb_rx;

		int ret = rte_pktmbuf_alloc_bulk(pktmbuf_pool, pkts_burst, burstSize);
		if (ret != 0) {
			rte_exit(EXIT_FAILURE, "rte_pktmbuf_alloc_bulk() failed");
		}

		for (unsigned int j = 0; j < burstSize; j++) {
			m = pkts_burst[j];
			rte_prefetch0(rte_pktmbuf_mtod(m, void *));
			// simple_forward(m);

			prepareAstraeusInit((pkts_burst[j]), srcIP, dstIP, 1025 + j, 4433 /*, sm*/);

			struct ether_hdr *eth = rte_pktmbuf_mtod(m, struct ether_hdr *);
			ether_addr_copy(&srcMac, &eth->s_addr);
			ether_addr_copy(&dstMac, &eth->d_addr);
			eth->ether_type = htons(0x0800);
		}
		srcIP++;

		// if (nb_rx > 0) {
		int sent = rte_eth_tx_burst(portId, 0, pkts_burst, burstSize);
		if (sent != static_cast<int>(burstSize)) {
			rte_exit(EXIT_FAILURE, "sent != burstSize");
		}
		if (sent) {
			port_statistics.tx += sent;
		}
		//}
	}
}

static int launch_one_lcore(__attribute__((unused)) void *dummy) {
	main_loop_astraeus();
	return 0;
}

/* display usage */
static void usage(const char *prgname) {
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
		   "  -p portid\n"
		   "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 "
		   "default, 86400 maximum)\n"
		   "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by "
		   "default)\n"
		   "      When enabled:\n"
		   "       - The source MAC address is replaced by the TX port MAC address\n"
		   "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n",
		prgname);
}

static void parse_mac(const char *macCStr, struct ether_addr &mac) {
	std::string macStr(macCStr);
	mac.addr_bytes[0] = static_cast<uint8_t>(stoi(macStr.substr(0, 2), nullptr, 16));
	mac.addr_bytes[1] = static_cast<uint8_t>(stoi(macStr.substr(3, 2), nullptr, 16));
	mac.addr_bytes[2] = static_cast<uint8_t>(stoi(macStr.substr(6, 2), nullptr, 16));
	mac.addr_bytes[3] = static_cast<uint8_t>(stoi(macStr.substr(9, 2), nullptr, 16));
	mac.addr_bytes[4] = static_cast<uint8_t>(stoi(macStr.substr(12, 2), nullptr, 16));
	mac.addr_bytes[5] = static_cast<uint8_t>(stoi(macStr.substr(15, 2), nullptr, 16));
}

static const char short_options[] = "p:" /* portid */
									"d:" /* destination mac */
	;

#define CMD_LINE_OPT_MAC_UPDATING "mac-updating"
#define CMD_LINE_OPT_NO_MAC_UPDATING "no-mac-updating"

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_MIN_NUM = 256,
};

static const struct option lgopts[] = {
	{CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0}, {NULL, 0, 0, 0}};

/* Parse the argument given in the command line of the application */
static int parse_args(int argc, char **argv) {
	int opt, ret;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, short_options, lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			portId = atoi(optarg);
			break;

		case 'd':
			parse_mac(optarg, dstMac);
			break;

		/* long options */
		case 0:
			break;

		default:
			usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind - 1] = prgname;

	ret = optind - 1;
	optind = 1; /* reset getopt lib */
	return ret;
}

/* Check the link status of all ports in up to 9s, and print them finally */
static void check_all_ports_link_status() {
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90  /* 9s (90 * 100ms) in total */
	uint8_t count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;

	printf("\nChecking link status");
	fflush(stdout);
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		if (force_quit)
			return;
		all_ports_up = 1;

		if (force_quit)
			return;
		memset(&link, 0, sizeof(link));
		rte_eth_link_get_nowait(portId, &link);
		/* print link status if flag set */
		if (print_flag == 1) {
			if (link.link_status)
				printf("Port %d Link Up - speed %u "
					   "Mbps - %s\n",
					(uint8_t)portId, (unsigned)link.link_speed,
					(link.link_duplex == ETH_LINK_FULL_DUPLEX) ? ("full-duplex")
															   : ("half-duplex\n"));
			else
				printf("Port %d Link Down\n", (uint8_t)portId);
			continue;
		}
		/* clear all_ports_up flag if any link down */
		if (link.link_status == ETH_LINK_DOWN) {
			all_ports_up = 0;
			break;
		}
		/* after finally printing all link status, get out */
		if (print_flag == 1)
			break;

		if (all_ports_up == 0) {
			printf(".");
			fflush(stdout);
			rte_delay_ms(CHECK_INTERVAL);
		}

		/* set the print_flag if all ports up or timeout */
		if (all_ports_up == 1 || count == (MAX_CHECK_TIME - 1)) {
			print_flag = 1;
			printf("done\n");
		}
	}
}

static void signal_handler(int signum) {
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n", signum);
		force_quit = true;
	}
}

int main(int argc, char **argv) {
	int ret;
	uint8_t nb_ports;
	unsigned lcore_id;

	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	/* parse application arguments (after the EAL ones) */
	ret = parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

	printf("MAC updating %s\n", mac_updating ? "enabled" : "disabled");

	port_conf.rxmode.split_hdr_size = 0;
	port_conf.rxmode.header_split = 0;   /**< Header Split disabled */
	port_conf.rxmode.hw_ip_checksum = 0; /**< IP checksum offload disabled */
	port_conf.rxmode.hw_vlan_filter = 0; /**< VLAN filtering disabled */
	port_conf.rxmode.jumbo_frame = 0;	/**< Jumbo Frame Support disabled */
	port_conf.rxmode.hw_strip_crc = 1;   /**< CRC stripped by hardware */
	port_conf.txmode.mq_mode = ETH_MQ_TX_NONE;

	/* convert to number of cycles */
	timer_period *= rte_get_timer_hz();

	/* create the mbuf pool */
	pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", NB_MBUF, MEMPOOL_CACHE_SIZE, 0,
		RTE_MBUF_DEFAULT_BUF_SIZE, rte_socket_id());
	if (pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	nb_ports = rte_eth_dev_count();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");

	/* init port */
	printf("Initializing port %u... ", (unsigned)portId);
	fflush(stdout);
	ret = rte_eth_dev_configure(portId, 1, 1, &port_conf);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n", ret,
			(unsigned)portId);

	ret = rte_eth_dev_adjust_nb_rx_tx_desc(portId, &nb_rxd, &nb_txd);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Cannot adjust number of descriptors: err=%d, port=%u\n", ret,
			(unsigned)portId);

	rte_eth_macaddr_get(portId, &srcMac);

	/* init one RX queue */
	fflush(stdout);
	ret = rte_eth_rx_queue_setup(
		portId, 0, nb_rxd, rte_eth_dev_socket_id(portId), NULL, pktmbuf_pool);
	if (ret < 0)
		rte_exit(
			EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n", ret, (unsigned)portId);

	/* init one TX queue on each port */
	fflush(stdout);
	ret = rte_eth_tx_queue_setup(portId, 0, nb_txd, rte_eth_dev_socket_id(portId), NULL);
	if (ret < 0)
		rte_exit(
			EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n", ret, (unsigned)portId);

	/* Initialize TX buffers */
	/* use burst instead
	tx_buffer[portid] =
		reinterpret_cast<rte_eth_dev_tx_buffer *>(rte_zmalloc_socket("tx_buffer",
			RTE_ETH_TX_BUFFER_SIZE(MAX_PKT_BURST), 0, rte_eth_dev_socket_id(portid)));
	if (tx_buffer[portid] == NULL)
		rte_exit(
			EXIT_FAILURE, "Cannot allocate buffer for tx on port %u\n", (unsigned)portid);

	rte_eth_tx_buffer_init(tx_buffer[portid], MAX_PKT_BURST);

	ret = rte_eth_tx_buffer_set_err_callback(tx_buffer[portid],
		rte_eth_tx_buffer_count_callback, &port_statistics[portid].dropped);
	if (ret < 0)
		rte_exit(EXIT_FAILURE,
			"Cannot set error callback for "
			"tx buffer on port %u\n",
			(unsigned)portid);
			*/

	/* Start device */
	ret = rte_eth_dev_start(portId);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n", ret, (unsigned)portId);

	printf("done: \n");

	rte_eth_promiscuous_enable(portId);

	printf("Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n\n", (unsigned)portId,
		srcMac.addr_bytes[0], srcMac.addr_bytes[1], srcMac.addr_bytes[2],
		srcMac.addr_bytes[3], srcMac.addr_bytes[4], srcMac.addr_bytes[5]);

	/* initialize port stats */
	memset(&port_statistics, 0, sizeof(port_statistics));

	check_all_ports_link_status();

	ret = 0;

	/* launch per-lcore init on every lcore */
	rte_eal_remote_launch(launch_one_lcore, NULL, 1);
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	printf("Closing port %d...", portId);
	rte_eth_dev_stop(portId);
	rte_eth_dev_close(portId);
	printf(" Done\n");

	printf("Bye...\n");

	return ret;
}
