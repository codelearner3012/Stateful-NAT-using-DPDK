/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2010-2016 Intel Corporation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_ip.h>
#include <rte_alarm.h>
#include <assert.h>
#include <pthread.h>
#include <readline/readline.h>

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 1;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 1024
#define RTE_TEST_TX_DESC_DEFAULT 1024
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

/* ethernet addresses of ports */
static struct rte_ether_addr l2fwd_ports_eth_addr[RTE_MAX_ETHPORTS];

/* mask of enabled ports */
static uint32_t l2fwd_enabled_port_mask = 0;

/* list of enabled ports */
static uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];

static unsigned int l2fwd_rx_queue_per_lcore = 1;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

static struct rte_eth_conf port_conf = {
	.rxmode = {
		.split_hdr_size = 0,
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;

/* TANVI: use static structures or see how dynamic structures are handled in DPDK */

#define SHELL_PROMPT "<NAT_DEVICE>$"
#define MAX_NAT_POOL_SIZE 256
#define SESSION_DURATION 20
#define CLEANUP_INTERVAL 500*10*1000
#define MARK_INTERVAL 500*10*1000
int debug = 0;

struct nat_pool_t{
	uint32_t  num_pool_addresses; 
	/* remove from the head of the queue */
	uint32_t head_index; 
	/* delete from the tail of the queue */
	uint32_t tail_index;
	/* 4 bytes padding */
	char padding[4];
	uint32_t nat_pool_list[MAX_NAT_POOL_SIZE];
} __rte_cache_aligned;

struct nat_pool_t nat_pool;

//static void print_nat_pool();
static void natpool_update(uint32_t s_nat_addr);

static void nat_init(const char* nat_pool_base, uint32_t blk_size);

static uint32_t nat_pool_lookup();

pthread_mutex_t f_lock;

/* hold onto it */
//pthread_rwlock_t mapping;
pthread_mutex_t mapping_lock;

enum mapping_status {
	ACTIVE, 
	DRAINING = 0x10,
	TIMED_OUT = 0x30
};

struct nat_mappings_t{
	uint32_t s_addr;
	uint32_t s_nat_addr;
	uint32_t d_addr;
	uint32_t pkt_cnt;
	uint32_t r_pkt_cnt;
	uint64_t curr_time;
	unsigned lcore_id;	
	unsigned status;
	struct nat_mappings_t *nxt_mapping;
	struct nat_mappings_t *prev_mapping;
	
} __rte_cache_aligned;

struct nat_mappings_stats_t {
	uint32_t n_incoming_packets;
	uint32_t n_outgoing_packets;
	uint32_t n_translated_packets;
	uint32_t n_current_mappings;
	//uint32_t n_nat_pool_addresses;
	uint32_t n_stale_mappings;
	uint32_t n_deleted_mappings;
} __rte_cache_aligned;

struct nat_mappings_t *head = NULL;

struct nat_mappings_t *tail = NULL;

struct nat_mappings_stats_t nat_stats;

static int nat_mapping_lookup(struct rte_ipv4_hdr *ipv4_hdr, unsigned lcore_id, struct nat_mappings_t **current_mapping);

static int nat_mapping_add(struct rte_ipv4_hdr *ipv4_hdr, unsigned lcore_id, struct nat_mappings_t **return_struct);

static void print_ip(uint32_t ip_addr);

static void print_nat_mappings();

//struct nat_mapping_t *nat_mapping_delete_and_update(struct nat_mappings_t *current);

/* define the flow table structure as well 
1. Linked list 
2. Hash table 
*/
/* TANVI code segment end */

struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 10; /* default period is 10 seconds */

/* Print out statistics on packets dropped */
static void
print_stats(void)
{
	uint64_t total_packets_dropped, total_packets_tx, total_packets_rx;
	unsigned portid;

	total_packets_dropped = 0;
	total_packets_tx = 0;
	total_packets_rx = 0;

	const char clr[] = { 27, '[', '2', 'J', '\0' };
	const char topLeft[] = { 27, '[', '1', ';', '1', 'H','\0' };

		/* Clear screen and move to top left */
	printf("%s%s", clr, topLeft);

	printf("\nPort statistics ====================================");

	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++) {
		/* skip disabled ports */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("\nStatistics for port %u ------------------------------"
			   "\nPackets sent: %24"PRIu64
			   "\nPackets received: %20"PRIu64
			   "\nPackets dropped: %21"PRIu64,
			   portid,
			   port_statistics[portid].tx,
			   port_statistics[portid].rx,
			   port_statistics[portid].dropped);

		total_packets_dropped += port_statistics[portid].dropped;
		total_packets_tx += port_statistics[portid].tx;
		total_packets_rx += port_statistics[portid].rx;
	}
	
	printf("\nAggregate statistics ==============================="
		   "\nTotal packets sent: %18"PRIu64
		   "\nTotal packets received: %14"PRIu64
		   "\nTotal packets dropped: %15"PRIu64,
		   total_packets_tx,
		   total_packets_rx,
		   total_packets_dropped);
	printf("\n====================================================\n");
}

static void
l2fwd_mac_updating(struct rte_mbuf *m, unsigned dest_portid)
{
	struct rte_ether_hdr *eth;
	void *tmp;

	eth = rte_pktmbuf_mtod(m, struct rte_ether_hdr *);

	/* 02:00:00:00:00:xx */
	tmp = &eth->d_addr.addr_bytes[0];
	*((uint64_t *)tmp) = 0x000000000002 + ((uint64_t)dest_portid << 40);

	/* src addr */
	rte_ether_addr_copy(&l2fwd_ports_eth_addr[dest_portid], &eth->s_addr);
}

static void print_ip(uint32_t ip_addr){
	unsigned char src_bytes[4];
	src_bytes[0] = ip_addr & 0xFF;
	src_bytes[1] = (ip_addr >> 8) & 0xFF;
	src_bytes[2] = (ip_addr >> 16) & 0xFF;
	src_bytes[3] = (ip_addr >> 24) & 0xFF;
	printf("%d.%d.%d.%d", src_bytes[3], src_bytes[2], src_bytes[1], src_bytes[0]);
}

/*static void show_session(struct rte_ipv4_hdr *ipv4_hdr, unsigned lcore_id){
	// src address 
	//unsigned char src_bytes[4];
	uint32_t src_addr = ntohl(ipv4_hdr->src_addr);
	//src_bytes[0] = src_addr & 0xFF;
	//src_bytes[1] = (src_addr >> 8) & 0xFF;
	//src_bytes[2] = (src_addr >>16) & 0xFF;
	//src_bytes[3] = (src_addr >> 24) & 0xFF;
	// dst addresss 
	uint32_t dst_addr = ntohl(ipv4_hdr->dst_addr);	
	//unsigned char dst_bytes[4];
	//dst_bytes[0] = dst_addr & 0XFF;
	//dst_bytes[1] = (dst_addr >> 8) & 0XFF;
	//dst_bytes[2] = (dst_addr >> 16) & 0XFF;
	//dst_bytes[3] = (dst_addr >> 24) & 0XFF;
	printf("\n lcore_id::%d ", lcore_id);
	printf(" Src addr:");
	print_ip(src_addr);
	printf(" Dst addr:");
	print_ip(dst_addr);
	printf("\n");
}*/

struct nat_mappings_t* nat_mapping_delete_and_update(struct nat_mappings_t *current){
	 /* update natpool */
	natpool_update(current->s_nat_addr);
	/* the current session is timed out */
	nat_stats.n_deleted_mappings += 1;
	if(current == head){
		if(current->nxt_mapping == NULL){
			free(current);
			head = NULL;
			tail = NULL;
			return NULL;
		}
		current->nxt_mapping->prev_mapping = NULL;
		head = current->nxt_mapping;
		free(current);
		return head;
	}
	else if(current->nxt_mapping == NULL){
		/* check for the last node in the list */
		current->prev_mapping->nxt_mapping = NULL;
		free(current);
		return NULL;
	}

	else {
		struct nat_mappings_t *temp_store = current->nxt_mapping;
		current->prev_mapping->nxt_mapping = current->nxt_mapping;
		current->nxt_mapping->prev_mapping = current->prev_mapping;
		free(current);
		return temp_store;
	}
}

static uint32_t 
nat_pool_lookup(void){
	/* if no addresses available in the NAT pool */
	if(nat_pool.num_pool_addresses == 0 || nat_pool.head_index > nat_pool.tail_index)
		return -1;
	nat_pool.num_pool_addresses -= 1;
	/* this is an extra check */
	if(nat_pool.head_index <= nat_pool.tail_index){
		uint32_t nat_pool_addr = nat_pool.nat_pool_list[nat_pool.head_index];
		nat_pool.head_index++;
		return nat_pool_addr;
	}
	else 
		return -1;
}

static int
nat_mapping_add(struct rte_ipv4_hdr *ipv4_hdr, unsigned lcore_id, struct nat_mappings_t **return_mapping){
	/* get a nat address from the pool */	
	struct nat_mappings_t *nat_entry = (struct nat_mappings_t*)malloc(sizeof(struct nat_mappings_t));
	nat_entry->s_addr = ntohl(ipv4_hdr->src_addr);
	nat_entry->d_addr = ntohl(ipv4_hdr->dst_addr);
	nat_entry->pkt_cnt = 1;
	nat_entry->r_pkt_cnt = 0;
	nat_entry->curr_time = rte_rdtsc();
	nat_entry->nxt_mapping = NULL;
	nat_entry->prev_mapping = NULL;
	nat_entry->lcore_id = lcore_id;
	nat_entry->status = ACTIVE;
	uint32_t ret = nat_pool_lookup();
	if(ret == -1){
		/* NAT pool exhausted */ 
		free(nat_entry);
		return -1;
	}
	nat_entry->s_nat_addr = ret;
	if(head == NULL){
		head = nat_entry;
		tail = head;
	}
	else {
		nat_entry->nxt_mapping = head;
		head->prev_mapping = nat_entry;
		head = nat_entry;
	}
	nat_stats.n_translated_packets += 1;
	nat_stats.n_current_mappings += 1;
	*return_mapping = nat_entry;
	return 0;
}

/* Return Map 
	0: No Mapping exists 
	1: Mapping exists 
	2: Mapping exists on a different lcore -> drop the packet 
	3: Forward flow already exists.
	TODO: create a NAT stats structure
*/
static int
nat_mapping_lookup(struct rte_ipv4_hdr *ipv4_hdr, unsigned lcore_id, struct nat_mappings_t **current_mapping){
	/* currently lookup the mapping based on the source ip address */
	//printf("lcore id : %d doing a NAT loop up \n", lcore_id);
	struct nat_mappings_t *current = head;
	current = head;
	uint32_t src_addr = ntohl(ipv4_hdr->src_addr);
	uint32_t dst_addr = ntohl(ipv4_hdr->dst_addr);
	while(current!=NULL){
		if(current->status == TIMED_OUT){
			/* keep deleting the nat mappings since you already acquired the locks */
			/*current->prev_mapping->nxt_mapping = current->nxt_mapping;
			current->nxt_mapping->prev_mapping = current->prev_mapping;
			current = current->nxt_mapping;
			natpool_update(current->s_nat_addr);
			free(current);*/
			current = nat_mapping_delete_and_update(current);
			continue; 
			
		}
		if(current->s_addr == src_addr){
			if(current->lcore_id == lcore_id && current->status == ACTIVE){
				*current_mapping = current;
				return 1;
			}
			else {
				/* same packed arrived on a different lcore discard it */
				return 2;
			}
		}
		else if(current->s_nat_addr == dst_addr){
			/* this is a reverse flow packet */
			if(debug)
				printf("its a hit \n");
			*current_mapping = current;
			return 3;
		}
		current = current->nxt_mapping;
	}
	*current_mapping = NULL;
	if(debug)
		printf("lcore id: %d unlocking thread \n", lcore_id);
	return 0;
}

static void 
natpool_update(uint32_t s_nat_addr){
	if(nat_pool.head_index>0){
		/* Add back values to the nat pool */
		nat_pool.head_index -= 1;
		nat_pool.num_pool_addresses += 1;
		nat_pool.nat_pool_list[nat_pool.head_index] = s_nat_addr;
	}
}


static void 
print_nat_mappings(){
	struct nat_mappings_t *current = head;
	printf("Printing NAT Mappings \n");
	uint64_t curr_tsc; //= rte_rdtsc();
	while(current!=NULL){
		if(current->status == ACTIVE){
			curr_tsc = rte_rdtsc();
			printf("Lcore id : %d Src Addr:", current->lcore_id);
			print_ip(current->s_addr);
			printf(" Nat Addr:");
			print_ip(current->s_nat_addr);
			printf(" --> Dest Addr:");
			print_ip(current->d_addr);
			uint64_t remaining_time = SESSION_DURATION - ((curr_tsc - current->curr_time)/rte_get_tsc_hz());
			printf(" Pkt Cnt: %d Session_duration %ld\n", current->pkt_cnt, remaining_time);
			printf(" Reverse Flow: Src Addr:");
			print_ip(current->d_addr);
			printf(" Dest Addr:");
			print_ip(current->s_nat_addr);
			printf(" Reverse Pkt Cnt: %d\n", current->r_pkt_cnt);
			printf("\n");
			current = current->nxt_mapping;
		}
		else {
			current = nat_mapping_delete_and_update(current);
			/* update natpool */
			//natpool_update(current->s_nat_addr);
			/* the current sessions is timed out */
			/*if(current == head){
				current->nxt_mapping->prev_mapping = NULL;
				head = current->nxt_mapping;
				free(current);
				current = head;
			}
			else {
				struct nat_mappings_t *temp_store = current->nxt_mapping;
				current->prev_mapping->nxt_mapping = current->nxt_mapping;
				current->nxt_mapping->prev_mapping = current->prev_mapping;
				free(current);
				current = temp_store;
			}*/
		}
	}
}

static void
increment_packet_count(struct nat_mappings_t *get_mapping, int flow){
	/* No need for locks here since we simply increment the packet count */
	struct nat_mappings_t *current = head; 
	/* TODO: generate a UUID to search for the index */ 
	while(current!= NULL){
		if(current->s_addr == get_mapping->s_addr){
			if(flow && current->lcore_id == get_mapping->lcore_id){
				if(debug)
					printf("foward count increment\n");
				current->pkt_cnt += 1;
			}
			else {
				current->r_pkt_cnt +=1;
			}
		}
		current = current->nxt_mapping;
	}
}

static void
l2fwd_simple_forward(struct rte_mbuf *m, unsigned portid, unsigned lcore_id)
{
	unsigned dst_port;
	int sent;
	int status = -1;
	struct rte_eth_dev_tx_buffer *buffer;

	struct rte_ipv4_hdr *ipv4_hdr;
        struct rte_ether_hdr *eth_hdr;
	eth_hdr = rte_pktmbuf_mtod(m, struct rte_ether_hdr*);
	ipv4_hdr = (struct rte_ipv4_hdr *)(eth_hdr + 1);        

	if (((ipv4_hdr->version_ihl)>>4) == 4){
		nat_stats.n_incoming_packets += 1;	
		if(debug){
			printf("Receiving source ip: ");
			print_ip(ipv4_hdr->src_addr);
			printf(" Destination ip ");
			print_ip(ipv4_hdr->dst_addr);
			printf("\n");
		}
		pthread_mutex_lock(&f_lock);
		/*if(ret == EBUSY)
			return;*/
		struct nat_mappings_t *get_mapping;
		status = nat_mapping_lookup(ipv4_hdr, lcore_id, &get_mapping);
		if(status == 0){
			get_mapping = NULL;
			int ret = nat_mapping_add(ipv4_hdr, lcore_id, &get_mapping);
			if(ret == -1){
				RTE_LOG(ERR, L2FWD, "NATPOOL Exhausted \n");
			}
			else {
				/* rewrite the packets and then send out the packet */
				ipv4_hdr->dst_addr = htonl(get_mapping->s_nat_addr);
				ipv4_hdr->src_addr = htonl(get_mapping->d_addr);
			}
		}
		else if(status == 1){
			/* increment the packet counter for the entry on the same lcore*/
			// pass the recieved mapping to increment the count 
			increment_packet_count(get_mapping, 1); 
			
		}
		else if(status == 3){
			/* increment the reverse packet counter for the entry */
			increment_packet_count(get_mapping, 0);
		
		}
		pthread_mutex_unlock(&f_lock);			
	}
	
	dst_port = l2fwd_dst_ports[portid];

	if (mac_updating)
		l2fwd_mac_updating(m, dst_port);
	buffer = tx_buffer[dst_port];
	if(status == 0) {
		/* foward this packet */
		//printf("sending the packet ");
		sent = rte_eth_tx_buffer(dst_port, 0, buffer, m);
		nat_stats.n_outgoing_packets += 1;
		if (sent)
			port_statistics[dst_port].tx += sent;
	}
}

/* main processing loop */
static void
l2fwd_main_loop(void)
{
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	int sent;
	unsigned lcore_id;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
	unsigned i, j, portid, nb_rx;
	struct lcore_queue_conf *qconf;
	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
			BURST_TX_DRAIN_US;
	struct rte_eth_dev_tx_buffer *buffer;

	prev_tsc = 0;
	timer_tsc = 0;

	lcore_id = rte_lcore_id();
	qconf = &lcore_queue_conf[lcore_id];

	//RTE_LOG(INFO, L2FWD, "core: %d n_rx_port %d\n", lcore_id, qconf->n_rx_port);

	if (qconf->n_rx_port == 0) {
		RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
		return;
	}

	RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

	for (i = 0; i < qconf->n_rx_port; i++) {

		portid = qconf->rx_port_list[i];
		RTE_LOG(INFO, L2FWD, "TANVI -- lcoreid=%u portid=%u\n", lcore_id,
			portid);

	}

	while (!force_quit) {

		cur_tsc = rte_rdtsc();

		/*
		 * TX burst queue drain
		 */
		diff_tsc = cur_tsc - prev_tsc;
		if (unlikely(diff_tsc > drain_tsc)) {

			for (i = 0; i < qconf->n_rx_port; i++) {

				portid = l2fwd_dst_ports[qconf->rx_port_list[i]];
				buffer = tx_buffer[portid];

				//RTE_LOG(INFO, L2FWD, "Draining the buffer \n");
				sent = rte_eth_tx_buffer_flush(portid, 0, buffer);
				if (sent)
					port_statistics[portid].tx += sent;

			}

			// if timer is enabled 
			/*if (timer_period > 0) {

				// advance the timer 
				timer_tsc += diff_tsc;

				// if timer has reached its timeout 
				if (unlikely(timer_tsc >= timer_period)) {

					//do this only on master core
					if (lcore_id == rte_get_master_lcore()) {
						//print_stats();
						print_nat_mappings();
						// reset the timer 
						timer_tsc = 0;
					}
				}
			}*/

			prev_tsc = cur_tsc;
		} 

		/*
		 * Read packet from RX queues
		 */
		for (i = 0; i < qconf->n_rx_port; i++) {

			portid = qconf->rx_port_list[i];
			nb_rx = rte_eth_rx_burst((uint8_t)portid, 0,
						 pkts_burst, MAX_PKT_BURST);

			port_statistics[portid].rx += nb_rx;
			//RTE_LOG(INFO, L2FWD, "TANVI lcore_id: %d n_rx_port: %d nb_rx:%d\n", lcore_id, qconf->n_rx_port, nb_rx);

			for (j = 0; j < nb_rx; j++) {
				m = pkts_burst[j];
				rte_prefetch0(rte_pktmbuf_mtod(m, struct ether_hdr *));
				l2fwd_simple_forward(m, portid, lcore_id);
			}
		}
	}
}

static int
l2fwd_launch_one_lcore(__attribute__((unused)) void *dummy)
{
	l2fwd_main_loop();
	return 0;
}

/* display usage */
static void
l2fwd_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n"
		   "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)\n"
		   "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)\n"
		   "      When enabled:\n"
		   "       - The source MAC address is replaced by the TX port MAC address\n"
		   "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n",
	       prgname);
}

static int
l2fwd_parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;

	if (pm == 0)
		return -1;

	return pm;
}

static unsigned int
l2fwd_parse_nqueue(const char *q_arg)
{
	char *end = NULL;
	unsigned long n;

	/* parse hexadecimal string */
	n = strtoul(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;
	if (n == 0)
		return 0;
	if (n >= MAX_RX_QUEUE_PER_LCORE)
		return 0;

	return n;
}

static int
l2fwd_parse_timer_period(const char *q_arg)
{
	char *end = NULL;
	int n;

	/* parse number string */
	n = strtol(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;
	if (n >= MAX_TIMER_PERIOD)
		return -1;

	return n;
}

static const char short_options[] =
	"p:"  /* portmask */
	"q:"  /* number of queues */
	"T:"  /* timer period */
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
	{ CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0},
	{NULL, 0, 0, 0}
};

/* Parse the argument given in the command line of the application */
static int
l2fwd_parse_args(int argc, char **argv)
{
	int opt, ret, timer_secs;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			l2fwd_enabled_port_mask = l2fwd_parse_portmask(optarg);
			if (l2fwd_enabled_port_mask == 0) {
				printf("invalid portmask\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* nqueue */
		case 'q':
			l2fwd_rx_queue_per_lcore = l2fwd_parse_nqueue(optarg);
			if (l2fwd_rx_queue_per_lcore == 0) {
				printf("invalid queue number\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* timer period */
		case 'T':
			timer_secs = l2fwd_parse_timer_period(optarg);
			if (timer_secs < 0) {
				printf("invalid timer period\n");
				l2fwd_usage(prgname);
				return -1;
			}
			timer_period = timer_secs;
			break;

		/* long options */
		case 0:
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 1; /* reset getopt lib */
	return ret;
}

/* Check the link status of all ports in up to 9s, and print them finally */
static void
check_all_ports_link_status(uint32_t port_mask)
{
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90 /* 9s (90 * 100ms) in total */
	uint16_t portid;
	uint8_t count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;
	int ret;

	printf("\nChecking link status");
	fflush(stdout);
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		if (force_quit)
			return;
		all_ports_up = 1;
		RTE_ETH_FOREACH_DEV(portid) {
			if (force_quit)
				return;
			if ((port_mask & (1 << portid)) == 0)
				continue;
			memset(&link, 0, sizeof(link));
			ret = rte_eth_link_get_nowait(portid, &link);
			if (ret < 0) {
				all_ports_up = 0;
				if (print_flag == 1)
					printf("Port %u link get failed: %s\n",
						portid, rte_strerror(-ret));
				continue;
			}
			/* print link status if flag set */
			if (print_flag == 1) {
				if (link.link_status)
					printf(
					"Port%d Link Up. Speed %u Mbps - %s\n",
						portid, link.link_speed,
				(link.link_duplex == ETH_LINK_FULL_DUPLEX) ?
					("full-duplex") : ("half-duplex\n"));
				else
					printf("Port %d Link Down\n", portid);
				continue;
			}
			/* clear all_ports_up flag if any link down */
			if (link.link_status == ETH_LINK_DOWN) {
				all_ports_up = 0;
				break;
			}
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

/* TODO: lock the structure while trying to print it */
/*static void 
print_nat_pool(){
	printf("Natpool head : %d\n", nat_pool.head_index);
	printf("Natpool tail : %d\n", nat_pool.tail_index);
	printf("Printing NATPOOL \n");
	uint32_t counter = nat_pool.head_index;
	//unsigned nat_bytes[4];
	while(counter < nat_pool.tail_index){
		//nat_bytes[0] = nat_pool.nat_pool_list[counter] & 0xFF;
		//nat_bytes[1] = (nat_pool.nat_pool_list[counter]>>8) & 0xFF;
		//nat_bytes[2] = (nat_pool.nat_pool_list[counter]>>16) & 0xFF;
		//nat_bytes[3] = (nat_pool.nat_pool_list[counter]>>24) & 0xFF;
		printf("natpool_addr : ");
		print_ip(nat_pool.nat_pool_list[counter]);
		printf("\n");
		counter++;	
	}
}*/

static void 
nat_init(const char *nat_pool_config, uint32_t block_size){
	/* initialize the nat pool */
	uint32_t block_counter;
	uint32_t pool_base = ntohl(inet_addr(nat_pool_config));
	nat_pool.num_pool_addresses = block_size;
	nat_pool.head_index = 0;
	if(block_size > MAX_NAT_POOL_SIZE)
		block_size = MAX_NAT_POOL_SIZE;
	for(block_counter = 0; block_counter < block_size; block_counter++)
		nat_pool.nat_pool_list[block_counter] = pool_base + block_counter; 
	nat_pool.tail_index = block_counter - 1;
	/* TODO: could allocate the nat pool prior for efficient performance */
	nat_stats.n_incoming_packets = 0;
	nat_stats.n_outgoing_packets = 0;
	nat_stats.n_translated_packets = 0;
	nat_stats.n_current_mappings = 0;
	//nat_stats.n_nat_pool_addresses = nat_pool.num_pool_addresses;
	nat_stats.n_stale_mappings = 0;
	nat_stats.n_deleted_mappings = 0;
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

static void 
print_nat_stats(){
	printf("---NAT Statistics---\n");
	printf("Number of incoming packets %d\n", nat_stats.n_incoming_packets);
	printf("Number of outgoing packets %d\n", nat_stats.n_outgoing_packets);
	printf("Number of translated packets %d\n", nat_stats.n_translated_packets);
	printf("Number of current mappings %d\n", nat_stats.n_current_mappings);
	printf("Number of nat pool addresses %d\n", nat_pool.num_pool_addresses);
	printf("Number of stale nat mappings %d\n", nat_stats.n_stale_mappings);
	printf("Number of deleted nat mappings %d\n", nat_stats.n_deleted_mappings);
}

static void 
clear_nat_stats(){
	nat_stats.n_incoming_packets = 0;
	nat_stats.n_outgoing_packets = 0;
	nat_stats.n_translated_packets = 0;
	nat_stats.n_current_mappings = 0;
	//nat_stats.n_nat_pool_addresses = 0;
	nat_stats.n_stale_mappings = 0;
	nat_stats.n_deleted_mappings = 0;
}

static void *
process_command(void *arg){
	char str[40];
	int n;
	struct nat_mappings_t *current;
	uint64_t curr_tsc, diff_tsc = 0;
	while (1){
		if ((n = read(0, str, 40)) > 0){
			if(strncmp(str, "show sessions",13) == 0){
				pthread_mutex_lock(&f_lock);
				/* since you already have a lock here then just delete some sessions yo */
				print_nat_mappings();
				pthread_mutex_unlock(&f_lock);
			}
			else if(strncmp(str, "show nat stats", 15)){
				print_nat_stats();
			}
			else if(strncmp(str, "clear nat stats", 15)){
				clear_nat_stats();
				print_nat_stats();
			}
			else
				continue;
		}
		//current = tail;
		/* Not acquiring a lock to delete the nat pool addresses */
		/*while(current != NULL){
			curr_tsc = rte_rdtsc();
			diff_tsc = (curr_tsc - current->curr_time)/rte_get_tsc_hz();
			if(debug == 1)
				printf("lcore_id:%d diff_tsc:%ld\n", rte_lcore_id(), diff_tsc);
			// optimize and dont traverse the whole list 
			if(diff_tsc >= SESSION_DURATION){
				current->status = TIMED_OUT;
			}
			current = current->prev_mapping;
		}*/
	}
	return NULL;
}

static void
mark_mapping_timeout(void *arg __rte_unused){
	rte_eal_alarm_set(MARK_INTERVAL, mark_mapping_timeout, NULL);	
	printf("Mark TIMED-OUT mappings alarm !\n");
	struct nat_mappings_t *current = tail;
        uint64_t curr_tsc, diff_tsc;
	while(current != NULL){
		curr_tsc = rte_rdtsc();
                diff_tsc = (curr_tsc - current->curr_time)/rte_get_tsc_hz();
                if(debug == 1)
			printf("lcore_id:%d diff_tsc:%ld\n", rte_lcore_id(), diff_tsc);
                // optimize and dont traverse the whole list 
            	if(diff_tsc >= SESSION_DURATION){
			current->status = TIMED_OUT;
			nat_stats.n_stale_mappings += 1;
                }
                current = current->prev_mapping;
        }

}
/*static void * 
timer_thread(void *arg __rte_unused){	
	struct nat_mappings_t *current = tail;
	uint64_t curr_tsc, diff_tsc = 0;
	while(1){
		//printf("Where are you ?\n");
		current = tail;
		while(current!=NULL){
			curr_tsc = rte_rdtsc();
			diff_tsc = (curr_tsc - current->curr_time)/rte_get_tsc_hz();
			printf("lcore_id %d diff_tsc: %ld\n", rte_lcore_id(), diff_tsc);
			if(diff_tsc >= SESSION_DURATION){
				current->status = TIMED_OUT;
			}
			current = current->prev_mapping;
		}
	}
	return NULL;
}*/

static void 
nat_mapping_clean_up(void *arg __rte_unused){
	if(debug == 0)
		printf("Here to clean up alarm! \n");
	rte_eal_alarm_set(CLEANUP_INTERVAL, nat_mapping_clean_up, NULL);
	int ret = pthread_mutex_lock(&f_lock);
	if(ret == EBUSY)
		return;
	/* check if the tail has timed out and only then traverse the list */
	struct nat_mappings_t *current = tail;
	while(current!=NULL){
		if(current->status == TIMED_OUT){
			nat_stats.n_deleted_mappings += 1;
			if(current == head){
				free(current);
				head = NULL;
				tail = NULL;
				current = head;
			}
			else if(current->nxt_mapping == NULL){
				/* If this is the last node */
				current->prev_mapping->nxt_mapping = NULL;
				current = current->prev_mapping;
			}
			else{
				/* If this a node in the middle */
				struct nat_mappings_t *temp_store = current->prev_mapping;
				current->prev_mapping->nxt_mapping = current->nxt_mapping;
				current->nxt_mapping->prev_mapping = current->prev_mapping;
				free(current);
				current = temp_store;
			}
		}
		else
			current = current->prev_mapping;
	}
	pthread_mutex_unlock(&f_lock);
}


int
main(int argc, char **argv)
{
	struct lcore_queue_conf *qconf;
	int ret;
	uint16_t nb_ports;
	uint16_t nb_ports_available = 0;
	uint16_t portid, last_port;
	unsigned lcore_id, rx_lcore_id;
	unsigned nb_ports_in_mask = 0;
	unsigned int nb_lcores = 0;
	unsigned int nb_mbufs;

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
	ret = l2fwd_parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

	printf("MAC updating %s\n", mac_updating ? "enabled" : "disabled");

		
	/* convert to number of cycles */
	timer_period *= rte_get_timer_hz();

	nb_ports = rte_eth_dev_count_avail();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");

	/* check port mask to possible port mask */
	if (l2fwd_enabled_port_mask & ~((1 << nb_ports) - 1))
		rte_exit(EXIT_FAILURE, "Invalid portmask; possible (0x%x)\n",
			(1 << nb_ports) - 1);
	

	/* reset l2fwd_dst_ports */
	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++)
		l2fwd_dst_ports[portid] = 0;
	last_port = 0;

	/*
	 * Each logical core is assigned a dedicated TX queue on each port.
	 */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		if (nb_ports_in_mask % 2) {
			l2fwd_dst_ports[portid] = last_port;
			l2fwd_dst_ports[last_port] = portid;
		}
		else
			last_port = portid;

		nb_ports_in_mask++;
	}
	if (nb_ports_in_mask % 2) {
		printf("Notice: odd number of ports in portmask.\n");
		l2fwd_dst_ports[last_port] = last_port;
	}

	rx_lcore_id = 0;
	qconf = NULL;

	/* Initialize the port/queue configuration of each logical core */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		/* get the lcore_id for this port */
		while (rte_lcore_is_enabled(rx_lcore_id) == 0 ||
		       lcore_queue_conf[rx_lcore_id].n_rx_port ==
		       l2fwd_rx_queue_per_lcore) {
			rx_lcore_id++;
			if (rx_lcore_id >= RTE_MAX_LCORE)
				rte_exit(EXIT_FAILURE, "Not enough cores\n");
		}

		if (qconf != &lcore_queue_conf[rx_lcore_id]) {
			/* Assigned a new logical core in the loop above. */
			qconf = &lcore_queue_conf[rx_lcore_id];
			nb_lcores++;
		}

		qconf->rx_port_list[qconf->n_rx_port] = portid;
		qconf->n_rx_port++;
		printf("Lcore %u: RX port %u\n", rx_lcore_id, portid);
	}

	nb_mbufs = RTE_MAX(nb_ports * (nb_rxd + nb_txd + MAX_PKT_BURST +
		nb_lcores * MEMPOOL_CACHE_SIZE), 8192U);

	/* create the mbuf pool */
	l2fwd_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", nb_mbufs,
		MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
		rte_socket_id());
	if (l2fwd_pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	/* Initialise each port */
	RTE_ETH_FOREACH_DEV(portid) {
		struct rte_eth_rxconf rxq_conf;
		struct rte_eth_txconf txq_conf;
		struct rte_eth_conf local_port_conf = port_conf;
		struct rte_eth_dev_info dev_info;

		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
			printf("Skipping disabled port %u\n", portid);
			continue;
		}
		nb_ports_available++;

		/* init port */
		printf("Initializing port %u... ", portid);
		fflush(stdout);

		ret = rte_eth_dev_info_get(portid, &dev_info);
		if (ret != 0)
			rte_exit(EXIT_FAILURE,
				"Error during getting device (port %u) info: %s\n",
				portid, strerror(-ret));

		if (dev_info.tx_offload_capa & DEV_TX_OFFLOAD_MBUF_FAST_FREE)
			local_port_conf.txmode.offloads |=
				DEV_TX_OFFLOAD_MBUF_FAST_FREE;
		ret = rte_eth_dev_configure(portid, 1, 1, &local_port_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
				  ret, portid);

		ret = rte_eth_dev_adjust_nb_rx_tx_desc(portid, &nb_rxd,
						       &nb_txd);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot adjust number of descriptors: err=%d, port=%u\n",
				 ret, portid);

		ret = rte_eth_macaddr_get(portid,
					  &l2fwd_ports_eth_addr[portid]);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot get MAC address: err=%d, port=%u\n",
				 ret, portid);

		/* init one RX queue */
		fflush(stdout);
		rxq_conf = dev_info.default_rxconf;
		rxq_conf.offloads = local_port_conf.rxmode.offloads;
		ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
					     rte_eth_dev_socket_id(portid),
					     &rxq_conf,
					     l2fwd_pktmbuf_pool);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n",
				  ret, portid);

		/* init one TX queue on each port */
		fflush(stdout);
		txq_conf = dev_info.default_txconf;
		txq_conf.offloads = local_port_conf.txmode.offloads;
		ret = rte_eth_tx_queue_setup(portid, 0, nb_txd,
				rte_eth_dev_socket_id(portid),
				&txq_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
				ret, portid);

		/* Initialize TX buffers */
		tx_buffer[portid] = rte_zmalloc_socket("tx_buffer",
				RTE_ETH_TX_BUFFER_SIZE(MAX_PKT_BURST), 0,
				rte_eth_dev_socket_id(portid));
		if (tx_buffer[portid] == NULL)
			rte_exit(EXIT_FAILURE, "Cannot allocate buffer for tx on port %u\n",
					portid);

		rte_eth_tx_buffer_init(tx_buffer[portid], MAX_PKT_BURST);

		ret = rte_eth_tx_buffer_set_err_callback(tx_buffer[portid],
				rte_eth_tx_buffer_count_callback,
				&port_statistics[portid].dropped);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
			"Cannot set error callback for tx buffer on port %u\n",
				 portid);

		ret = rte_eth_dev_set_ptypes(portid, RTE_PTYPE_UNKNOWN, NULL,
					     0);
		if (ret < 0)
			printf("Port %u, Failed to disable Ptype parsing\n",
					portid);
		/* Start device */
		ret = rte_eth_dev_start(portid);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
				  ret, portid);

		printf("done: \n");

		ret = rte_eth_promiscuous_enable(portid);
		if (ret != 0)
			rte_exit(EXIT_FAILURE,
				 "rte_eth_promiscuous_enable:err=%s, port=%u\n",
				 rte_strerror(-ret), portid);

		printf("Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n\n",
				portid,
				l2fwd_ports_eth_addr[portid].addr_bytes[0],
				l2fwd_ports_eth_addr[portid].addr_bytes[1],
				l2fwd_ports_eth_addr[portid].addr_bytes[2],
				l2fwd_ports_eth_addr[portid].addr_bytes[3],
				l2fwd_ports_eth_addr[portid].addr_bytes[4],
				l2fwd_ports_eth_addr[portid].addr_bytes[5]);

		/* initialize port stats */
		memset(&port_statistics, 0, sizeof(port_statistics));
	}

	if (!nb_ports_available) {
		rte_exit(EXIT_FAILURE,
			"All available ports are disabled. Please set portmask.\n");
	}

	check_all_ports_link_status(l2fwd_enabled_port_mask);
	
	/* configure the NAT POOL statically */ 
	const char *natpool_config = "100.1.2.0";
	/* TODO: configure later */ 
	uint32_t block_size = 256;
	nat_init(natpool_config, block_size);
	//print_nat_pool();
	pthread_t t_id, t_id1;
	rte_ctrl_thread_create(&t_id, "process_command", NULL, process_command, NULL);
	//rte_ctrl_thread_create(&t_id1, "timer_thread", NULL, timer_thread, NULL);
	
	/* set an alarm for deletion of nat mappings */
	ret = 0;
	ret = rte_eal_alarm_set(CLEANUP_INTERVAL, nat_mapping_clean_up, NULL);
	if(ret<0)
		printf("Failed to setup cleaup alarm \n");
	ret = 0;
	ret = rte_eal_alarm_set(MARK_INTERVAL, mark_mapping_timeout, NULL);
	if(ret<0)
		printf("Failed to setup marking up alarm \n");


	ret = 0;
	/* This is where the logic starts : launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(l2fwd_launch_one_lcore, NULL, CALL_MASTER);
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	RTE_ETH_FOREACH_DEV(portid) {
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("Closing port %d...", portid);
		rte_eth_dev_stop(portid);
		rte_eth_dev_close(portid);
		printf(" Done\n");
	}
	printf("Bye...\n");

	return ret;
}
