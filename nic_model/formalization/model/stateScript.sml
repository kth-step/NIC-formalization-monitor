open HolKernel Parse boolLib bossLib;
open wordsLib;
open CPPI_RAMTheory;

val _ = new_theory "state";

val _ = Datatype `it_abstract_state =
  | it_power_on
  | it_reset
  | it_initialize_hdp_cp
  | it_initialized`;

val _ = Datatype `it_state = <|
  state : it_abstract_state;
  tx0_hdp_initialized : bool;
  rx0_hdp_initialized : bool;
  tx0_cp_initialized : bool;
  rx0_cp_initialized : bool
  |>`;

val _ = Datatype `tx_abstract_state =
  | tx_idle
  | tx_fetch_next_bd
  | tx_issue_next_memory_read_request
  | tx_process_memory_read_reply
  | tx_post_process
  | tx_clear_owner_and_hdp
  | tx_write_cp`;

val _ = Datatype `tx_state = <|
  state : tx_abstract_state;
  current_bd_pa : 32 word;
  current_bd : bd_data;
  expects_sop : bool;
  sum_buffer_length : 32 word;
  sop_packet_length : 32 word;
  sop_bd_pa : 32 word;
  pa_of_next_memory_buffer_byte : 32 word;
  eop_bd_pa : 32 word;
  number_of_buffer_bytes_left_to_request : 32 word;
  interrupt : bool|>`;

val _ = Datatype `tx_environment = <|
  assert_interrupt : bool |>`;

val _ = Datatype `td_abstract_state =
  | td_idle
  | td_set_eoq
  | td_set_td
  | td_clear_owner_and_hdp
  | td_write_cp`;

val _ = Datatype `td_state = <|
  state : td_abstract_state
  |>`;

val _ = Datatype `td_environment = <|
  set_eoq : bool;
  assert_interrupt : bool |>`;

val _ = Datatype `rx_abstract_state =
  | rx_idle
  | rx_fetch_next_bd
  | rx_issue_next_memory_write_request
  | rx_write_packet_error
  | rx_write_rx_vlan_encap
  | rx_write_from_port
  | rx_write_eop_buffer_length
  | rx_set_eop_eop
  | rx_set_eop_eoq_or_write_sop_buffer_offset
  | rx_write_sop_buffer_offset
  | rx_write_sop_buffer_length
  | rx_set_sop_sop
  | rx_write_sop_pass_crc
  | rx_write_sop_long
  | rx_write_sop_short
  | rx_write_sop_mac_ctl
  | rx_write_sop_packet_length
  | rx_set_sop_eop_overrun_or_clear_sop_owner_and_hdp
  | rx_clear_sop_owner_and_hdp
  | rx_write_cp`;

val _ = Datatype `rx_state = <|
  state : rx_abstract_state;
  frame : 8 word list;
  frame_length : 32 word;
  frame_bytes_left : 32 word;
  current_bd_pa : 32 word;
  current_bd : bd_data;
  overrun : bool;
  current_bd_number_of_stored_bytes : 32 word;
  next_buffer_byte_address : 32 word;
  current_bd_size : 32 word;
  sop_bd_pa : 32 word;
  sop_buffer_offset : 32 word;
  sop_buffer_used_length : 32 word;
  eop_bd_pa : 32 word;
  interrupt : bool|>`;

val _ = Datatype `overrun_case = sop_overrun | eop_overrun | both_overrun`;

val _ = Datatype `rx_environment = <|
  received_frame : 8 word list;
  packet_error : 2 word;
  rx_vlan_encap : 1 word;
  from_port : 3 word;
  pass_crc : 1 word;
  long : 1 word;
  short : 1 word;
  mac_ctl : 1 word;
  sop_eop_both_overrun: overrun_case;
  assert_interrupt : bool
  |>`;

val _ = Datatype `rd_abstract_state =
  | rd_idle
  | rd_set_sop
  | rd_set_eop
  | rd_set_eoq
  | rd_set_td
  | rd_clear_owner_and_hdp
  | rd_write_cp`;

val _ = Datatype `rd_state = <|
  state : rd_abstract_state
  |>`;

val _ = Datatype `rd_environment = <|
  set_sop : bool;
  set_eop : bool;
  set_eoq : bool;
  assert_interrupt : bool
  |>`;

val _ = Datatype `nic_regs = <|
  TX_TEARDOWN : 3 word;
  RX_TEARDOWN : 3 word;
  CPDMA_SOFT_RESET : 1 word;
  DMACONTROL : 16 word;
  RX_BUFFER_OFFSET : 16 word;
  TX0_HDP : 32 word;
  TX0_CP : 32 word;
  RX0_HDP : 32 word;
  RX0_CP : 32 word;
  CPPI_RAM : 13 word -> 8 word|>`;

val _ = Datatype `nic_state = <|
  dead : bool;
  interrupt : bool;
  regs : nic_regs;
  it : it_state;
  tx : tx_state;
  td : td_state;
  rx : rx_state;
  rd : rd_state|>`;

val _ = Datatype `memory_request = <|
  pa : 32 word;
  v : 8 word option|>`;

val _ = Datatype `scheduled_automaton =
  | initialize
  | transmit
  | receive
  | teardown_transmission
  | teardown_reception`;

val _ = Datatype `reg_write_environment = <|
  tx0_hdp_value : 32 word;
  rx0_hdp_value : 32 word;
  tx0_cp_deassert_interrupt : bool;
  rx0_cp_deassert_interrupt : bool
  |>`;

val _ = Datatype `environment = <|
  scheduler : scheduled_automaton;
  reg_write : reg_write_environment;
  reg_read : 32 word;
  tx : tx_environment;
  td : td_environment;
  rx : rx_environment;
  rd : rd_environment
  |>`;

type_abbrev ("nic_delta_type", ``: nic_state -> nic_state``);

val _ = export_theory();
