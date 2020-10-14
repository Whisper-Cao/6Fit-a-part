/*Created by Yifeng Cao. Snippet extracted from rest of the code on Oct/11/2020.
This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License.
This code is used as a part of the implementation for the ICNP 2020 paper titled: 6Fit-A-Part: A Protocol for Physical Distancing on 
a Custom Wearable Device. The code should be used in conjugation with the library provided by Decawave for TREK1000:
 https://www.decawave.com/software/.

If you find the below code useful in any way, please cite the paper: 
"6Fit-A-Part: A Protocol for Physical Distancing on a Custom Wearable Device", Yifeng Cao, Ashutosh Dhekne, Mostafa Ammar,
The 28th annual edition of the IEEE International Conference on Network Protocols (ICNP 2020)
Refer to the paper for more technical details. Current information about the project will be maintained at www.6fitapart.com
*/
#define APP_NAME "6Fit-a-part"

#include "compiler.h"
#include "port.h"
#include "instance.h"
#include "deca_types.h"
#include "deca_spi.h"
#include "stdio.h"
#include "deca_device_api.h"
#include "deca_regs.h"
#include "lcd.h"
#include "time.h"
#include "stdlib.h"

#define TX_ANT_DLY 16436
#define RX_ANT_DLY 16436
#define TYPICAL_RX_TIMEOUT 40000 
#define FINAL_MSG_TS_LEN 8
#define POLL_MSG_TS_LEN 8
#define ANY_MSG_TS_LEN 8
#define SRC_IDX 2
#define DST_IDX 3
#define SEQ_IDX 4
#define MAX_SLOT_IDX 6
#define NUM_DST_IDX 7
#define POLL_MSG_POLL_TX_TS_IDX 7
#define FINAL_MSG_FINAL_TX_TS_IDX 8
#define FINAL_TX_TS_GAP  9

#define NONE_TYPE 0x00
#define ERR_TYPE 0xFE
#define NOT_MY_PACKET_TYPE 0xAA
#define POLL_MSG_TYPE 0x20
#define RESP_MSG_TYPE 0x21
#define FINAL_MSG_TYPE 0x22
#define FINAL_MSG_ALL_TYPE 0x23
#define DIST_EST_MSG_TYPE 0x24
#define RESP_AGAIN_MSG_TYPE 0x25
#define FINAL_AGAIN_MSG_TYPE 0x26
#define DEBUG_PRINT 0

#define SYS_STATUS_ALL_RX_ERR  (SYS_STATUS_RXPHE | SYS_STATUS_RXFCE | SYS_STATUS_RXRFSL | SYS_STATUS_RXSFDTO \
                                | SYS_STATUS_RXRFTO | SYS_STATUS_RXPTO | SYS_STATUS_AFFREJ | SYS_STATUS_LDEERR)

#define TYPE_INDEX 0

#define MAX_RESP_NUM 20
#define MAX_SLOT_COEFFICIENT 3
#define RESP_AGAIN_SCHEME 1
#define NUM_BOARDS 20
#define MAX_NODE_ID NUM_BOARDS

#define MAX_DATA_BUF_SIZE 2000
#define DATA_BUF_MARGIN 100
#define CIR_REPORT_START_FROM 730
#define CIR_REPORT_END_BEFORE 100
#define NCIR_FULL 1016

#define CHAN_CONFIG config_chan2

static dwt_config_t config_chan2 = { 2, /* Channel number. */
DWT_PRF_64M, /* Pulse repetition frequency. */
DWT_PLEN_1024, /* Preamble length. */
DWT_PAC32, /* Preamble acquisition chunk size. Used in RX only. */
9, /* TX preamble code. Used in TX only. */
9, /* RX preamble code. Used in RX only. */
1, /* Use non-standard SFD (Boolean) */
DWT_BR_6M8, /* Data rate. */
//DWT_PHRMODE_STD, /* PHY header mode. */
DWT_PHRMODE_EXT,
(1025 + 64 - 32) /* SFD timeout (preamble length + 1 + SFD length - PAC size). Used in RX only. */
//(4161) /* SFD timeout (preamble length + 1 + SFD length - PAC size). Used in RX only. */
};

static void generic_send(uint8 *buffer_to_send, int buffer_size, int delayed, uint8 skipBoard);
static void generic_receive(uint16);
void peer_logic();
int wrapper_rx_enable(uint16);
static void any_msg_set_ts(uint8* msg, uint64 send_time);
static void any_msg_set_ts_uint32(uint8* msg, uint32 msg_uint32);
static uint64 get_tx_timestamp_u64(void);
static uint64 get_rx_timestamp_u64(void);
static void final_msg_get_ts(const uint8 *ts_field, uint64 *ts);
static void final_msg_set_ts(uint8 *ts_field, uint64 ts);
static void poll_msg_set_ts(uint8 *ts_field, uint64 ts);
static void poll_msg_get_ts(const uint8 *ts_field, uint64 *ts);
static void any_msg_get_ts(const uint8 *ts_field, uint64 *ts);
static void any_msg_get_ts_uint32(const uint8 *ts_field, uint32 *ts);

static uint8 tx_poll_msg[20] = {POLL_MSG_TYPE, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
static uint8 rx_resp_msg[36] = {RESP_MSG_TYPE, 0x02, 0, 0, 0, 0, 0};
static uint8 tx_final_msg[128] = {FINAL_MSG_TYPE, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

static uint8 rx_poll_msg[16] = {POLL_MSG_TYPE, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
static uint8 tx_resp_msg[32] = {RESP_MSG_TYPE, 0x02, 0, 0, 0, 0, 0};
static uint8 rx_final_msg[48] = {FINAL_MSG_TYPE, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

typedef enum states{STATE_IDLE, STATE_POLL, STATE_RESP_EXPECTED, STATE_FINAL_SEND, STATE_RESP_SEND, STATE_FINAL_EXPECTED, STATE_OTHER_POLL_EXPECTED,
STATE_RESP_AGAIN_SEND, STATE_FINAL_AGAIN_EXPECTED, STATE_RESP_AGAIN_EXPECTED, STATE_FINAL_AGAIN_SEND, STATE_SLEEP} STATES;
typedef enum send_modes{SEND_IMMEDIATE, SEND_DELAY_FIXED, SEND_DELAY_BOARDID, SEND_SHORT_DELAY_BOARDID, SEND_LONG_DELAY_BOARDID, SEND_DELAY_GIVEN, SEND_DELAY_RANDOM} SEND_MODES;

uint64 current_poll_tx_ts = 0;
uint64 current_poll_rx_ts = 0;
uint64 current_resp_tx_ts = 0;
uint64 current_resp_rx_ts = 0;
uint64 current_final_tx_ts = 0;
uint64 current_final_rx_ts = 0;

uint64 current_resp_rx_ts_all[NUM_BOARDS+1] = {0};

int recorded_resp_nodes[MAX_RESP_NUM] = {0};
int n_resp_count = 0;

uint8 tx_report_buffer[13] = {0};

int cur_max_slot = 20;
int recvd_max_slot = 20;
int cur_max_slot_round2 = 20;
int recvd_max_slot_round2 = 20;
int which_slot = 0;

int RX_TIMEOUT = TYPICAL_RX_TIMEOUT;
static uint8 rx_buffer[RX_BUF_LEN];
static uint32 status_reg = 0;
char longer_str[512] = { 0 };
uint8 CIRData2[4 * NCIR_FULL + 1 + 5];
int16 RealData[1021];
int16 ImaginaryData[1021];
uint8 datalarge[MAX_DATA_BUF_SIZE];


int32 board_id = 0;
uint32 resp_rx_timestamps[MAX_NODE_ID];
uint32 current_time = 0;
uint32 rx_starttime = 0;
double elapsed_time = 0;

uint64 resp_expect_starttime = 0; 
double resp_expect_elapsedtime = 0; 
uint64 poll_expect_starttime = 0; 
double poll_expect_elapsedtime = 0; 
uint64 final_expect_starttime = 0; 
double final_expect_elapsedtime = 0; 
uint64 resp_again_expect_starttime = 0; 
double resp_again_expect_elapsedtime = 0; 
uint64 final_again_expect_starttime = 0; 
double final_again_expect_elapsedtime = 0;
uint64 sleep_starttime = 0; 
double sleep_elapsedtime = 0; 


int main(void) {
	/* Start with board specific hardware init. */
	peripherals_init();
	spi_peripheral_init();
	Sleep(1000);
	initLCD();
	lcd_display_str(APP_NAME);
	Sleep(1000);
	reset_DW1000(); 
	spi_set_rate_low();
	dwt_initialise(DWT_LOADUCODE);
	spi_set_rate_high();

	int twr_status_n = 0;
	uint32 smtx_reg = dwt_read32bitreg(SYS_CFG_ID);
	uint32 tx_power_setting = dwt_read32bitreg(TX_POWER_ID);
	smtx_reg = smtx_reg | (SYS_CFG_DIS_STXP);
	tx_power_setting = (tx_power_setting & 0xFF0000FF) | (0x001F1F00) ; // Power control is important to prevent the packet reception from nodes far away
	dwt_write32bitreg(SYS_CFG_ID, smtx_reg);
	dwt_write32bitreg(TX_POWER_ID, tx_power_setting);

    board_id = is_switch_on(TA_SW1_3)<<4 |
        is_switch_on(TA_SW1_4)<<3 |
        is_switch_on(TA_SW1_5)<<2 |
        is_switch_on(TA_SW1_6)<<1 |
        is_switch_on(TA_SW1_7);
    h = sprintf(dist_str, "Node %d", board_id);
    send_usbmessage(dist_str, h);
    lcd_display_str(dist_str);
    usb_run();
    Sleep(1000);
    if (board_id<MAX_NODE_ID){
        peer_logic();
    }
    break;
}

void peer_logic()
{
	Sleep(1000); 
	int twr_status_n = 0;
	int current_state = STATE_POLL;
	int skip_receive = 1;
	uint16 seq_to_use = 0;
	double time_unit = 1.0 / (128*499.2e6); // seconds
	double resp_expect_timeout = 0, poll_expect_remaintime = 0, other_poll_expect_timeout = 0, final_expect_timeout = 0, resp_again_expect_timeout = 0, sleep_timeout = 0, final_again_expect_timeout;
	uint16 rx_timeout; 
	int first_start = 1;
	int poll_from_node = -1, resp_from_node = -1, final_from_node = -1;
	int expect_final_from = -1;
	int poll_collision_penalty = 0;

	while(end_proto != 1)
	{
		current_time = dwt_readsystimestamphi32();
		elapsed_time = (((uint64)(current_time - rx_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
		if (!skip_receive)
		{
			generic_receive(rx_timeout);
		}
		else
		{
			skip_receive = 0;
		}
		switch(current_state){
			case STATE_IDLE:
				break;
			case STATE_POLL:
				master_seq++;
				send_poll_all(master_seq);
				resp_expect_starttime = dwt_readsystimestamphi32();// timeout is us
				resp_expect_timeout = cur_max_slot * SLOT_LENGTH + RESP_EXPECT_GRACE_TIME;
				rx_timeout = resp_expect_timeout;
				current_state = STATE_RESP_EXPECTED;
				break;
			case STATE_RESP_EXPECTED:
				resp_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - resp_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
				if(resp_expect_elapsedtime > resp_expect_timeout){
					current_state = STATE_FINAL_SEND;
					skip_receive = 1;
				}else{
					if(rx_buffer[0] == RESP_MSG_TYPE){
						resp_from_node = receive_resp();
					}else if(rx_buffer[0] == POLL_MSG_TYPE){
						poll_collision_penalty = (rx_buffer[SRC_IDX] > board_id) ? poll_collision_penalty + OTHER_POLL_EXPECTED_RANDOMNESS :poll_collision_penalty - OTHER_POLL_EXPECTED_RANDOMNESS;
					}
					resp_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - resp_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
					rx_timeout =  resp_expect_timeout - resp_expect_elapsedtime;
				}
				break;
			case STATE_FINAL_SEND:
				send_final(FINAL_MSG_TYPE);
				if(RESP_AGAIN_SCHEME != 1){ /* other poll expected state*/
					poll_expect_starttime = dwt_readsystimestamphi32();// timeout is us
					other_poll_expect_timeout = OTHER_POLL_EXPECTED_TIMEOUT + poll_collision_penalty * OTHER_POLL_EXPECTED_RANDOMNESS_LENGTH ; // prevent deadlock
					poll_collision_penalty = 0;
					rx_timeout = (RX_TIMEOUT > other_poll_expect_timeout)? other_poll_expect_timeout : RX_TIMEOUT;
					current_state = STATE_OTHER_POLL_EXPECTED;
				}else{/*final again expected state*/
					resp_again_expect_starttime = dwt_readsystimestamphi32();// timeout is us
					resp_again_expect_timeout = cur_max_slot_round2 * SLOT_LENGTH + RESP_EXPECT_GRACE_TIME;//timeout must be smaller than 65535
					rx_timeout = resp_again_expect_timeout;
					current_state = STATE_RESP_AGAIN_EXPECTED;
				}
				break;
			case STATE_RESP_AGAIN_EXPECTED:
				resp_again_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - resp_again_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
				if(resp_again_expect_elapsedtime > resp_again_expect_timeout){
					current_state = STATE_FINAL_AGAIN_SEND;
					skip_receive = 1;
				}else{
					if(rx_buffer[0] == RESP_AGAIN_MSG_TYPE){
						resp_from_node = receive_resp();
					}
					resp_again_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - resp_again_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
					rx_timeout =  resp_again_expect_timeout - resp_again_expect_elapsedtime;
				}
				break;
			case STATE_FINAL_AGAIN_SEND:
				send_final(FINAL_AGAIN_MSG_TYPE);
				poll_expect_starttime = dwt_readsystimestamphi32();// timeout is us
				other_poll_expect_timeout = OTHER_POLL_EXPECTED_TIMEOUT + poll_collision_penalty * OTHER_POLL_EXPECTED_RANDOMNESS_LENGTH +(poll_expect_starttime % OTHER_POLL_EXPECTED_RANDOMNESS) *OTHER_POLL_EXPECTED_RANDOMNESS_LENGTH ; // prevent deadlock
				other_poll_expect_timeout = global_constrain(other_poll_expect_timeout, GLOBAL_MIN_OTHER_POLL_EXPECTED_TIMEOUT, GLOBAL_MAX_OTHER_POLL_EXPECTED_TIMEOUT);
				poll_collision_penalty = 0;
				rx_timeout = (RX_TIMEOUT > other_poll_expect_timeout)? other_poll_expect_timeout : RX_TIMEOUT;
				current_state = STATE_OTHER_POLL_EXPECTED;
			case STATE_OTHER_POLL_EXPECTED: //generic receive
				poll_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - poll_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
				if(poll_expect_elapsedtime > other_poll_expect_timeout){

					current_state = STATE_POLL;
					skip_receive = 1;
				}else{
					if(rx_buffer[0] == POLL_MSG_TYPE){
						poll_from_node = poll_accept();
						expect_final_from = poll_from_node;
						current_state = STATE_RESP_SEND;
						/* Freeze the time in STATE_OTHER_POLL_EXPECT*/
						poll_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - poll_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
						poll_expect_remaintime = other_poll_expect_timeout - poll_expect_elapsedtime;

						skip_receive = 1;
					}
					poll_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - poll_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
					rx_timeout = (RX_TIMEOUT > other_poll_expect_timeout - poll_expect_elapsedtime)? other_poll_expect_timeout - poll_expect_elapsedtime : RX_TIMEOUT;
				}
				break;
			case STATE_RESP_SEND:// from STATE_OTHER_POLL_EXPECTED
				if(poll_from_node != -1){
					resp_send(poll_from_node, which_slot, RESP_MSG_TYPE);
					final_expect_starttime = dwt_readsystimestamphi32();// timeout is us
					final_expect_timeout = recvd_max_slot * SLOT_LENGTH + FINAL_EXPECT_GRACE_TIME - (which_slot + 1) * SLOT_LENGTH;
					rx_timeout = final_expect_timeout;
					current_state = STATE_FINAL_EXPECTED;

				}
				break;
			case STATE_FINAL_EXPECTED:// from STATE_RESP_SEND
				final_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - final_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
				if(final_expect_elapsedtime > final_expect_timeout){
					current_state = STATE_OTHER_POLL_EXPECTED;
					other_poll_expect_timeout = poll_expect_remaintime;
					poll_expect_starttime = dwt_readsystimestamphi32();// timeout is us
					rx_timeout =  (RX_TIMEOUT > other_poll_expect_timeout)? other_poll_expect_timeout : RX_TIMEOUT;
				}else{/*Time in, final*/
					if(rx_buffer[0] == FINAL_MSG_TYPE && rx_buffer[SRC_IDX] == expect_final_from ){
						final_from_node = record_ranging(FINAL_MSG_TYPE);
						if(final_from_node != -1){/* in the list and seq is right, go to sleep*/
							current_state = STATE_SLEEP;
							sleep_timeout = recvd_max_slot_round2 * SLOT_LENGTH + FINAL_EXPECT_GRACE_TIME;
							sleep_starttime = dwt_readsystimestamphi32();// timeout is us
							skip_receive = 1;
							break;
						}else{
							if(RESP_AGAIN_SCHEME == 1){
								prepare_resp_again(); /*Use the final as the poll*/
								current_state = STATE_RESP_AGAIN_SEND;
								skip_receive = 1;
								/* Freeze the time in STATE_OTHER_POLL_EXPECT*/
								break;
							}

						}

					}
					final_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - final_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
					rx_timeout = final_expect_timeout - final_expect_elapsedtime;
				}

				break;
			case STATE_RESP_AGAIN_SEND:
				resp_send(expect_final_from, which_slot, RESP_AGAIN_MSG_TYPE);
				final_again_expect_starttime = dwt_readsystimestamphi32();// timeout is us
				final_again_expect_timeout = recvd_max_slot_round2 * SLOT_LENGTH + FINAL_EXPECT_GRACE_TIME - (which_slot + 1) * SLOT_LENGTH;
				rx_timeout = final_again_expect_timeout;
				current_state = STATE_FINAL_AGAIN_EXPECTED;
				break;
			case STATE_FINAL_AGAIN_EXPECTED:
				final_again_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - final_again_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
				if(final_again_expect_elapsedtime > final_again_expect_timeout){

					current_state = STATE_OTHER_POLL_EXPECTED;
					other_poll_expect_timeout = poll_expect_remaintime;
					poll_expect_starttime = dwt_readsystimestamphi32();// timeout is us
					rx_timeout =  (RX_TIMEOUT > other_poll_expect_timeout)? other_poll_expect_timeout : RX_TIMEOUT;
				}else{
					if(rx_buffer[0] == FINAL_AGAIN_MSG_TYPE && rx_buffer[SRC_IDX] == expect_final_from ){
						final_from_node = record_ranging(FINAL_AGAIN_MSG_TYPE);
						if(final_from_node != -1){/* in the list and seq is right, go to sleep*/
							current_state = STATE_OTHER_POLL_EXPECTED;
							other_poll_expect_timeout = poll_expect_remaintime;
							poll_expect_starttime = dwt_readsystimestamphi32();// timeout is us
							rx_timeout =  (RX_TIMEOUT > other_poll_expect_timeout)? other_poll_expect_timeout : RX_TIMEOUT;
							break;
						}
					}
					final_again_expect_elapsedtime = (((uint64)(dwt_readsystimestamphi32() - final_again_expect_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
					rx_timeout = final_again_expect_timeout - final_again_expect_elapsedtime;
				}
				break;
			case STATE_SLEEP:
				sleep_elapsedtime =(((uint64)(dwt_readsystimestamphi32() - sleep_starttime) << 8)) * DWT_TIME_UNITS * 1000000;
				if(sleep_elapsedtime > sleep_timeout){
					current_state = STATE_OTHER_POLL_EXPECTED;
					other_poll_expect_timeout = poll_expect_remaintime;
					poll_expect_starttime = dwt_readsystimestamphi32();// timeout is us
					rx_timeout =  (RX_TIMEOUT > other_poll_expect_timeout)? other_poll_expect_timeout : RX_TIMEOUT;
				}else{
					skip_receive = 1;
				}
				break;
		}
	}
}

//Broadcast poll
void send_poll_all(int16 seq_to_use)
{
	int twr_status_n = 0;
	//Prepare the poll packet
	poll_tx_ts[board_id] = 0;
	tx_poll_msg[SEQ_IDX] = seq_to_use & 0xFF;
	tx_poll_msg[SEQ_IDX+1] = (seq_to_use >> 8) & 0xFF;
	tx_poll_msg[SRC_IDX] = board_id;
	tx_poll_msg[DST_IDX] = BROADCAST_ID;
	tx_poll_msg[MAX_SLOT_IDX] = cur_max_slot;

	//Fill in the hop1node information in the poll message

	uint32 current_time = dwt_readsystimestamphi32();
	uint32 next_scheduled_time = current_time;
	next_scheduled_time = next_scheduled_time + (ONE_MSEC * WAIT_BEFORE_POLL);
	dwt_setdelayedtrxtime(next_scheduled_time);
	poll_tx_ts[board_id] = (((uint64) (next_scheduled_time & 0xFFFFFFFE)) << 8)
					+ TX_ANT_DLY;
	poll_msg_set_ts(&tx_poll_msg[POLL_MSG_POLL_TX_TS_IDX], poll_tx_ts[board_id]);
	generic_send(tx_poll_msg, sizeof(tx_poll_msg), SEND_DELAY_GIVEN, 0);
}

int receive_resp()
{
	int src_node = rx_buffer[SRC_IDX];
	uint16 resp_seq_no = rx_buffer[SEQ_IDX] + (rx_buffer[SEQ_IDX+1] << 8);
	if(resp_seq_no != master_seq || n_resp_count >= MAX_RESP_NUM){
		return -1;
	}else{
		recorded_resp_nodes[n_resp_count] = src_node;
		current_resp_rx_ts_all[src_node] = get_rx_timestamp_u64();
		n_resp_count++;
		return rx_buffer[SRC_IDX];
	}
}


void send_final(uint8 type)
{
	int twr_status_n = 0;
	uint16 seq_no = master_seq;

	tx_final_msg[TYPE_INDEX] = type;
	tx_final_msg[SRC_IDX] = board_id;
	tx_final_msg[DST_IDX] = BROADCAST_ID;
	tx_final_msg[SEQ_IDX] = seq_no & 0xFF;
	tx_final_msg[SEQ_IDX+1] = (seq_no >> 8) & 0xFF;
	tx_final_msg[NUM_DST_IDX] = n_resp_count;

	/*Send final*/
	int dstNode;
	int ts_idx_start = FINAL_MSG_FINAL_TX_TS_IDX + FINAL_MSG_TS_LEN;
	int idx_step = 9;

	int idx = ts_idx_start;
	for(int i = 0; i < n_resp_count; i++){
		dstNode = recorded_resp_nodes[i];
		tx_final_msg[idx] = dstNode;
		any_msg_set_ts(&tx_final_msg[idx+1], current_resp_rx_ts_all[dstNode]);//POLL TX MSG
		idx += FINAL_TX_TS_GAP;
	}


	/*Update cur_max_slot*/
	cur_max_slot = n_resp_count * MAX_SLOT_COEFFICIENT;
	cur_max_slot = (cur_max_slot > MAX_SLOT_COEFFICIENT) ? cur_max_slot : MAX_SLOT_COEFFICIENT;
	cur_max_slot =(cur_max_slot < GLOBAL_MAX_SLOT) ? cur_max_slot : GLOBAL_MAX_SLOT;
	cur_max_slot_round2 = get_max_slot_round2(cur_max_slot, n_resp_count);

	tx_final_msg[MAX_SLOT_IDX] = cur_max_slot_round2;

	uint32 current_time = dwt_readsystimestamphi32();
	uint32 next_scheduled_time = current_time;
	next_scheduled_time = next_scheduled_time + (ONE_MSEC * WAIT_BEFORE_POLL);
	dwt_setdelayedtrxtime(next_scheduled_time);
	current_final_tx_ts = (((uint64) (next_scheduled_time & 0xFFFFFFFE)) << 8)
					+ TX_ANT_DLY;
	any_msg_set_ts(&tx_final_msg[FINAL_MSG_FINAL_TX_TS_IDX], current_final_tx_ts);//FINAL TX MSG
	generic_send(tx_final_msg, sizeof(tx_final_msg), SEND_DELAY_GIVEN, 0);
	n_resp_count = 0;
}

int poll_accept()
{
	int poll_from_node = rx_buffer[SRC_IDX];

	if(poll_from_node > NUM_BOARDS){
		return -1;
	}
	recvd_max_slot = rx_buffer[MAX_SLOT_IDX];
	which_slot = (dwt_readsystimestamphi32() / 10) % recvd_max_slot;
	poll_msg_get_ts(&rx_buffer[POLL_MSG_POLL_TX_TS_IDX], &current_poll_tx_ts); // get poll tx time
	int src_node = rx_buffer[SRC_IDX];
	current_poll_rx_ts = get_rx_timestamp_u64();
	tag_expect_seq[poll_from_node] = rx_buffer[SEQ_IDX] + (rx_buffer[SEQ_IDX+1] << 8);

	int twr_status_n = 0;
	return poll_from_node;
}

void resp_send(uint8 respond_to_node, int slot, uint8 type)
{
	int twr_status_n = 0;
	tx_resp_msg[0] = type;
	uint16 rx_seq = rx_buffer[SEQ_IDX] + (rx_buffer[SEQ_IDX+1] << 8);;
	/* Write and send the response message.*/
	tx_resp_msg[SRC_IDX] = board_id;
	tx_resp_msg[DST_IDX] = respond_to_node;//respond_to_node;
	tx_resp_msg[SEQ_IDX] = rx_seq & 0xFF;
	tx_resp_msg[SEQ_IDX+1] = (rx_seq>>8) & 0xFF;

	int delayed_ms = (slot + 1) * (SLOT_LENGTH / 1000);
	uint32 next_scheduled_time = dwt_readsystimestamphi32() + (ONE_MSEC * delayed_ms);
	dwt_setdelayedtrxtime(next_scheduled_time);

	generic_send(tx_resp_msg, sizeof(tx_resp_msg), SEND_DELAY_GIVEN, 0);
	current_resp_tx_ts = (((uint64) (next_scheduled_time & 0xFFFFFFFE)) << 8)
					+ TX_ANT_DLY;
}

int prepare_resp_again(){
	int final_from_node = rx_buffer[SRC_IDX];
	any_msg_get_ts(&rx_buffer[FINAL_MSG_FINAL_TX_TS_IDX], &current_poll_tx_ts); // use this final as a new poll
	current_poll_rx_ts = get_rx_timestamp_u64();//poll reception time
	which_slot = (dwt_readsystimestamphi32() / 10) % recvd_max_slot_round2;

	return final_from_node;
}

int  record_ranging(int type)
{
	int twr_status_n = 0;
	int n=0;
	uint32 poll_rx_ts_32, final_rx_ts_32;
	double Ra, Rb, Da, Db;
	double tof_dtu;
	int final_from_node = rx_buffer[SRC_IDX];
	uint16 rx_seq =rx_buffer[SEQ_IDX] + (rx_buffer[SEQ_IDX+1] << 8);
	recvd_max_slot_round2 = rx_buffer[MAX_SLOT_IDX];

	if (rx_seq != tag_expect_seq[final_from_node])
	{
		twr_status_n = sprintf(longer_str,
						"Final from wrong seq %02x. I am: %d, Expected final for: %02x, Got from: %d",
						rx_seq, board_id, tag_expect_seq[final_from_node], rx_buffer[SRC_IDX]);
		send_usbmessage(longer_str, twr_status_n);
		usb_run();

		return -1;
	}

	int n_dst = rx_buffer[NUM_DST_IDX];
	int my_resp_ts_idx = -1;
	int idx = FINAL_MSG_FINAL_TX_TS_IDX + FINAL_MSG_TS_LEN;
	for(int i = 0; i < n_dst; i++){
		if(rx_buffer[idx] == board_id){
			my_resp_ts_idx = idx;
			break;
		}else{
			idx = idx + FINAL_TX_TS_GAP;
		}
	}
	if(my_resp_ts_idx == -1){
		if(rx_buffer[0] == FINAL_MSG_TYPE){
			twr_status_n = sprintf(longer_str,"Round 1: I am not in the list.");
		}else{
			twr_status_n = sprintf(longer_str,"Round 2: I am not in the list.");
		}

		send_usbmessage(longer_str, twr_status_n);
		usb_run();
		return -1;
	}

	/* Retrieve response transmission and final reception timestamps. */
	any_msg_get_ts(&rx_buffer[my_resp_ts_idx+1], &current_resp_rx_ts); // get resp tx time
	any_msg_get_ts(&rx_buffer[FINAL_MSG_FINAL_TX_TS_IDX], &current_final_tx_ts); // get poll tx time
	current_final_rx_ts = get_rx_timestamp_u64();

	/* Compute time of flight. 32-bit subtractions give correct answers even if clock has wrapped. See NOTE 10 below. */
	Ra = (double) ((uint32)current_resp_rx_ts - (uint32)current_poll_tx_ts);
	Rb = (double) ((uint32)current_final_rx_ts - (uint32)current_resp_tx_ts);
	Da = (double) ((uint32)current_final_tx_ts - (uint32)current_resp_rx_ts);
	Db = (double) ((uint32)current_resp_tx_ts - (uint32)current_poll_rx_ts);

	//Ensure that all timestamps are cleaned up

	tof_dtu = ((Ra * Rb - Da * Db)
			/ (Ra + Rb + Da + Db));
	tof = tof_dtu * DWT_TIME_UNITS;
	distance = tof * SPEED_OF_LIGHT;
	uint32 current_time_dist = dwt_readsystimestamphi32();
	
	double distance_to_correct;
	if (CALCULATE_TWR == 1) {
		if (CHAN_CONFIG.dataRate == DWT_BR_6M8)
		{
			//1.31 for channel 2 and 1.51 for channel 5
			if (CHAN_CONFIG.chan == 5) {
				distance_to_correct = distance / 1.51;
			} else //channel 2
			{
				distance_to_correct = distance / 1.31;
			}
		} else {
			distance_to_correct = distance;
		}
		distance = distance
				- dwt_getrangebias(CHAN_CONFIG.chan,
						(float) distance_to_correct,
						CHAN_CONFIG.prf);
		current_dist_report_mm = (uint32) (distance * 1000);
	}

	//Print out the current range:
	char longer_str[512] = { 0 };
	uint16 firstPath = dwt_read16bitoffsetreg(RX_TIME_ID,RX_TIME_FP_INDEX_OFFSET);
	uint16 firstPath_integer = (firstPath & 0xFFC0) >> 6;
	uint16 firstPath_fraction = (firstPath & 0x003F);

	int is_final_again = (type == FINAL_AGAIN_MSG_TYPE) ? 1 : 0;
	twr_status_n =  sprintf(longer_str, "%d,%lu, %llu, %lu,%lu, %lu,%lu,%lu,%lu,%lu,%lu,%lu,%lu,%lu,d00", final_from_node, (uint32)rx_seq, current_final_rx_ts,  (uint32)current_dist_report_mm, is_final_again, firstPath_integer, firstPath_fraction,
			maxNoiseDiag, firstPathAmp1Diag, stdNoiseDiag, firstPathAmp2Diag, firstPathAmp3Diag, maxGrowthCIRDiag,rxPreamCount);
	send_usbmessage(longer_str, twr_status_n);
	usb_run();

	n = 0;
	for (int i = CIR_REPORT_START_FROM; i < NCIR_FULL - CIR_REPORT_END_BEFORE; i++) {
		RealData[i] = CIRData2[(i * 4) + 2] << 8
				| CIRData2[(i * 4) + 1];
		ImaginaryData[i] = CIRData2[(i * 4) + 4] << 8
				| CIRData2[(i * 4) + 3];
		n += sprintf((char*) &datalarge[0] + n,
				"%lu,%d,%d,y%d\r\n", rx_seq, RealData[i],
				ImaginaryData[i], i + 1);
		if (n > (MAX_DATA_BUF_SIZE - DATA_BUF_MARGIN)) {
			Sleep(5);
			send_usbmessage(&datalarge[0], n);
			usb_run();
			n = 0;
		}
	}
		if (n > 0) {
		Sleep(5);
		send_usbmessage(&datalarge[0], n);
		usb_run();
		n = 0;
	}


	return final_from_node;
}

static void generic_send(uint8 *buffer_to_send, int buffer_size, int delayed, uint8 skipBoad)
{
	int twr_status_n;
	dwt_writetxdata(buffer_size, buffer_to_send, 0);
	dwt_writetxfctrl(buffer_size, 0);

	if (DEBUG_PRINT) {
	//if(buffer_to_send[0] == POLL_MSG_TYPE) {
		uint32 current_time_end = dwt_readsystimestamphi32();
		twr_status_n =
				sprintf(longer_str,
						"generic sending type: %02x at %llu with flag = %02x, seq: %02x", buffer_to_send[0], ((uint64) dwt_readsystimestamphi32()) << 8, delayed, buffer_to_send[SEQ_IDX]);
		send_usbmessage(longer_str, twr_status_n);
		usb_run();
	}
	uint32 next_scheduled_time = dwt_readsystimestamphi32();
	uint8 dwt_starttx_arg;
	if (delayed == SEND_IMMEDIATE) {
		next_scheduled_time = next_scheduled_time + (ONE_MSEC * MIN_GAP_BETWEEN_PACKETS);
		//dwt_setdelayedtrxtime(next_scheduled_time);
		dwt_starttx_arg = DWT_START_TX_IMMEDIATE;
	}
	if (delayed == SEND_DELAY_FIXED) {
		next_scheduled_time = next_scheduled_time + (ONE_MSEC * MIN_GAP_BETWEEN_PACKETS);
		dwt_setdelayedtrxtime(next_scheduled_time);
		dwt_starttx_arg = DWT_START_TX_DELAYED;
	}
	if (delayed == SEND_DELAY_BOARDID) {
		uint8 this_node_id = board_id;
		if (skipBoad!=0 && board_id > skipBoad)
		{
			this_node_id--;
		}
		next_scheduled_time = next_scheduled_time + (ONE_MSEC*3)+(ONE_MSEC * BOARD_SEPARATION_GAP * (this_node_id-1)); //Tring node_id-1 June29, 2018
		dwt_setdelayedtrxtime(next_scheduled_time);
		dwt_starttx_arg = DWT_START_TX_DELAYED;
	}
	if (delayed == SEND_SHORT_DELAY_BOARDID) {
		uint8 this_node_id = board_id;
		if (skipBoad!=0 && board_id > skipBoad)
		{
			this_node_id--;
		}
		next_scheduled_time = next_scheduled_time + (ONE_MSEC * BOARD_SEPARATION_SHORT_GAP * (this_node_id));
		dwt_setdelayedtrxtime(next_scheduled_time);
		dwt_starttx_arg = DWT_START_TX_DELAYED;
	}
	if (delayed == SEND_LONG_DELAY_BOARDID) {
		uint8 this_node_id = board_id;
		if (skipBoad!=0 && board_id > skipBoad)
		{
			this_node_id--;
		}
		next_scheduled_time = next_scheduled_time + (ONE_MSEC * BOARD_SEPARATION_LONG_GAP * (this_node_id));
		dwt_setdelayedtrxtime(next_scheduled_time);
		dwt_starttx_arg = DWT_START_TX_DELAYED;
	}
	if (delayed == SEND_DELAY_GIVEN) {
		//The actual delay has been set by the calling function
		dwt_starttx_arg = DWT_START_TX_DELAYED;
	}
	if (delayed == SEND_DELAY_RANDOM) {

		dwt_starttx_arg = DWT_START_TX_DELAYED;

	}
	dwt_forcetrxoff();
	rx_is_enabled = 0;
	if (dwt_starttx(dwt_starttx_arg) == DWT_ERROR) {
	//if (dwt_starttx(DWT_START_TX_IMMEDIATE) == DWT_ERROR) {
		twr_status_n = sprintf(longer_str,
				"dwt error while generic sending %02x", buffer_to_send[0]);
		send_usbmessage(longer_str, twr_status_n);
		usb_run();
		if (dwt_starttx(DWT_START_TX_IMMEDIATE) == DWT_ERROR) {
			twr_status_n = sprintf(longer_str,
							"again dwt error while generic sending %02x immediate", buffer_to_send[0]);
			send_usbmessage(longer_str, twr_status_n);
			usb_run();
		}
	}
	/* Poll DW1000 until TX frame sent event set. See NOTE 8 below. */
	while (!(dwt_read32bitreg(SYS_STATUS_ID) & SYS_STATUS_TXFRS)) {
	};
	dwt_write32bitreg(SYS_STATUS_ID, SYS_STATUS_TXFRS);
	dwt_write32bitreg(SYS_STATUS_ID, CLEAR_ALLTX_EVENTS);

	if (DEBUG_PRINT) {
		twr_status_n = sprintf(longer_str, "generic message type %02x, len=%d, sent at %llu, , seq: %02x", buffer_to_send[0], buffer_size, ((uint64) dwt_readsystimestamphi32()) << 8, buffer_to_send[SEQ_IDX]);
		send_usbmessage(longer_str, twr_status_n);
		usb_run();
	}

}

int wrapper_rx_enable(uint16 rx_timeout)
{
	int rxret = 0;
	if (rx_is_enabled==1)
	{

	} else {
		dwt_setrxtimeout(rx_timeout);
		rxret = dwt_rxenable(0);
		rx_is_enabled = 1;
	}
	return rxret;
}


static void generic_receive(uint16 rx_timeout)
{
	int twr_status_n = 0;
	int rxret = wrapper_rx_enable(rx_timeout);
	uint32 temp=0;
	while (!((status_reg = dwt_read32bitreg(SYS_STATUS_ID))//
						& (SYS_STATUS_RXFCG | SYS_STATUS_ALL_RX_ERR))) {

	};
	rx_is_enabled = 0;
	if (status_reg & SYS_STATUS_RXFCG) {

		uint32 frame_len;

		/* Clear good RX frame event in the DW1000 status register. */
		dwt_write32bitreg(SYS_STATUS_ID, SYS_STATUS_RXFCG);
		uint32 clear = 0; // will clear any events seen
		clear |= status_reg & CLEAR_ALLRXERROR_EVENTS;
		dwt_write32bitreg(SYS_STATUS_ID, clear);

		/* A frame has been received, read it into the local buffer. */
		frame_len = dwt_read32bitreg(RX_FINFO_ID) & RX_FINFO_RXFL_MASK_1023;
		if (frame_len <= RX_BUFFER_LEN) {
			dwt_readrxdata(rx_buffer, frame_len, 0);

		}
		else {
			twr_status_n = sprintf(longer_str, "Frame too big %lu", frame_len);
			send_usbmessage(longer_str, twr_status_n);
			usb_run();
		}
		if (DEBUG_PRINT==1)
		{
			twr_status_n = sprintf(longer_str, "frame at (%llu): type %02x %02x %02x %02x", ((uint64) dwt_readsystimestamphi32()) << 8, rx_buffer[0], rx_buffer[2], rx_buffer[3], rx_buffer[4]);
			send_usbmessage(longer_str, twr_status_n);
			usb_run();
		}
		if (rx_buffer[TYPE_INDEX] == FINAL_MSG_TYPE || rx_buffer[TYPE_INDEX] == FINAL_MSG_ALL_TYPE) {
			dwt_readaccdata(CIRData2, 4 * NCIR_FULL, 0);
		}
		dwt_rxdiag_t rx_frame_diagnostics;
		dwt_readdignostics(&rx_frame_diagnostics);

		maxNoiseDiag = rx_frame_diagnostics.maxNoise;
		firstPathAmp1Diag = rx_frame_diagnostics.firstPathAmp1;
		stdNoiseDiag = rx_frame_diagnostics.stdNoise;
		firstPathAmp2Diag = rx_frame_diagnostics.firstPathAmp2;
		firstPathAmp3Diag = rx_frame_diagnostics.firstPathAmp3;
		maxGrowthCIRDiag = rx_frame_diagnostics.maxGrowthCIR;
		rxPreamCount = rx_frame_diagnostics.rxPreamCount;
		//Does the frame belong to me?

		if (rx_buffer[DST_IDX] == board_id || rx_buffer[DST_IDX] == BROADCAST_ID) {
			if (DEBUG_PRINT==1 || STABILITY_PRINT ==1)
			{
				twr_status_n = sprintf(longer_str, "my packet at (%llu): type %02x %02x %02x %02x", ((uint64) dwt_readsystimestamphi32()) << 8, rx_buffer[0], rx_buffer[2], rx_buffer[3], rx_buffer[4]);
				send_usbmessage(longer_str, twr_status_n);
				usb_run();
			}
			return;
		}
		else {
			sneak_packet = rx_buffer[0];
			rx_buffer[0]=NOT_MY_PACKET_TYPE;
			return;
		}
	} else if (status_reg & (SYS_STATUS_RXRFTO | SYS_STATUS_RXPTO)) {
		uint32 clear = 0; // will clear any events seen
		clear |= status_reg & CLEAR_ALLRXERROR_EVENTS;
		clear |= status_reg & CLEAR_ALLRXGOOD_EVENTS;
		dwt_write32bitreg(SYS_STATUS_ID, clear);
		rx_buffer[0]=NONE_TYPE;
	}
	else {
		uint32 clear = 0; // will clear any events seen
		clear |= status_reg & CLEAR_ALLRXERROR_EVENTS;
		dwt_write32bitreg(SYS_STATUS_ID, clear);
		rx_buffer[0]=ERR_TYPE;
	}
}

static uint64 get_tx_timestamp_u64(void) {
	uint8 ts_tab[5];
	uint64 ts = 0;
	int i;
	dwt_readtxtimestamp(ts_tab);
	for (i = 4; i >= 0; i--) {
		ts <<= 8;
		ts |= ts_tab[i];
	}
	return ts;
}

static uint64 get_rx_timestamp_u64(void) {
	uint8 ts_tab[5];
	uint64 ts = 0;
	int i;
	dwt_readrxtimestamp(ts_tab);
	for (i = 4; i >= 0; i--) {
		ts <<= 8;
		ts |= ts_tab[i];
	}
	return ts;
}

static void final_msg_get_ts(const uint8 *ts_field, uint64 *ts) {
	int i;
	*ts = 0;
	for (i = 0; i < FINAL_MSG_TS_LEN; i++) {
		*ts += ((uint64)ts_field[i]) << (i * 8);
	}
}
static void poll_msg_get_ts(const uint8 *ts_field, uint64 *ts) {
	int i;
	*ts = 0;
	for (i = 0; i < POLL_MSG_TS_LEN; i++) {
		*ts += ((uint64)ts_field[i]) << (i * 8);
	}
}

static void any_msg_get_ts(const uint8 *ts_field, uint64 *ts) {
	int i;
	*ts = 0;
	for (i = 0; i < ANY_MSG_TS_LEN; i++) {
		*ts += ((uint64)ts_field[i]) << (i * 8);
	}
}

static void any_msg_get_ts_uint32(const uint8 *ts_field, uint32 *ts) {
	int i;
	*ts = 0;
	for (i = 0; i < 4; i++) {
		*ts += ((uint32)ts_field[i]) << (i * 8);
	}
}

static void final_msg_set_ts(uint8 *ts_field, uint64 ts) {
	int i;
	for (i = 0; i < FINAL_MSG_TS_LEN; i++) {
		ts_field[i] = (uint8) ts;
		ts >>= 8;
	}
}

static void poll_msg_set_ts(uint8 *ts_field, uint64 ts) {
	int i;
	for (i = 0; i < POLL_MSG_TS_LEN; i++) {
		ts_field[i] = (uint8) ts;
		ts >>= 8;
	}
}

static void any_msg_set_ts(uint8 *ts_field, uint64 ts) {
	int i;
	for (i = 0; i < ANY_MSG_TS_LEN; i++) {
		ts_field[i] = (uint8) ts;
		ts >>= 8;
	}
}

static void any_msg_set_ts_uint32(uint8 *ts_field, uint32 ts) {
	int i;
	for (i = 0; i < 4; i++) {
		ts_field[i] = (uint8) ts;
		ts >>= 8;
	}
}

