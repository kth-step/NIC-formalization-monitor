open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "rx_state_definitions";

(* Definitions classifying the states of the reception automaton. *)
val RX_STATE_IDLE_def = Define `
  RX_STATE_IDLE (nic : nic_state) = (nic.rx.state = rx_idle)`;

val RX_STATE_FETCH_NEXT_BD_def = Define `
  RX_STATE_FETCH_NEXT_BD (nic : nic_state) = (nic.rx.state = rx_fetch_next_bd)`;

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def = Define `
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST (nic : nic_state) =
  (nic.rx.state = rx_issue_next_memory_write_request)`;

val RX_STATE_WRITE_PACKET_ERROR_def = Define `
  RX_STATE_WRITE_PACKET_ERROR (nic : nic_state) = (nic.rx.state = rx_write_packet_error)`;

val RX_STATE_WRITE_RX_VLAN_ENCAP_def = Define `
  RX_STATE_WRITE_RX_VLAN_ENCAP (nic : nic_state) = (nic.rx.state = rx_write_rx_vlan_encap)`;

val RX_STATE_WRITE_FROM_PORT_def = Define `
  RX_STATE_WRITE_FROM_PORT (nic : nic_state) = (nic.rx.state = rx_write_from_port)`;

val RX_STATE_WRITE_EOP_BUFFER_LENGTH_def = Define `
  RX_STATE_WRITE_EOP_BUFFER_LENGTH (nic : nic_state) =
  (nic.rx.state = rx_write_eop_buffer_length)`;

val RX_STATE_SET_EOP_EOP_def = Define `
  RX_STATE_SET_EOP_EOP (nic : nic_state) = (nic.rx.state = rx_set_eop_eop)`;

val RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_def = Define `
  RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET (nic : nic_state) =
  (nic.rx.state = rx_set_eop_eoq_or_write_sop_buffer_offset)`;

val RX_STATE_WRITE_SOP_BUFFER_OFFSET_def = Define `
  RX_STATE_WRITE_SOP_BUFFER_OFFSET (nic : nic_state) =
  (nic.rx.state = rx_write_sop_buffer_offset)`;

val RX_STATE_WRITE_SOP_BUFFER_LENGTH_def = Define `
  RX_STATE_WRITE_SOP_BUFFER_LENGTH (nic : nic_state) =
  (nic.rx.state = rx_write_sop_buffer_length)`;

val RX_STATE_SET_SOP_SOP_def = Define `
  RX_STATE_SET_SOP_SOP (nic : nic_state) = (nic.rx.state = rx_set_sop_sop)`;

val RX_STATE_WRITE_SOP_PASS_CRC_def = Define `
  RX_STATE_WRITE_SOP_PASS_CRC (nic : nic_state) = (nic.rx.state = rx_write_sop_pass_crc)`;

val RX_STATE_WRITE_SOP_LONG_def = Define `
  RX_STATE_WRITE_SOP_LONG (nic : nic_state) = (nic.rx.state = rx_write_sop_long)`;

val RX_STATE_WRITE_SOP_SHORT_def = Define `
  RX_STATE_WRITE_SOP_SHORT (nic : nic_state) = (nic.rx.state = rx_write_sop_short)`;

val RX_STATE_WRITE_SOP_MAC_CTL_def = Define `
  RX_STATE_WRITE_SOP_MAC_CTL (nic : nic_state) = (nic.rx.state = rx_write_sop_mac_ctl)`;

val RX_STATE_WRITE_SOP_PACKET_LENGTH_def = Define `
  RX_STATE_WRITE_SOP_PACKET_LENGTH (nic : nic_state) = (nic.rx.state = rx_write_sop_packet_length)`;

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_def = Define `
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP (nic : nic_state) =
  (nic.rx.state = rx_set_sop_eop_overrun_or_clear_sop_owner_and_hdp)`;

val RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def = Define `
  RX_STATE_CLEAR_SOP_OWNER_AND_HDP (nic : nic_state) =
  (nic.rx.state = rx_clear_sop_owner_and_hdp)`;

val RX_STATE_WRITE_CP_def = Define `
  RX_STATE_WRITE_CP (nic : nic_state) = (nic.rx.state = rx_write_cp)`;

val RX_BD_QUEUE_EMPTY_def = Define `
  RX_BD_QUEUE_EMPTY nic = (nic.rx.sop_bd_pa = 0w)`;

val RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY_def = Define `
  RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY nic =
  RX_STATE_WRITE_CP nic /\ ~RX_BD_QUEUE_EMPTY nic`;



(*Start of classification of states.*)
val RX_STATE_WRITE_CURRENT_BD_PA_def = Define `
  RX_STATE_WRITE_CURRENT_BD_PA (nic : nic_state) =
  RX_STATE_WRITE_PACKET_ERROR nic \/
  RX_STATE_WRITE_RX_VLAN_ENCAP nic \/
  RX_STATE_WRITE_FROM_PORT nic`;

val RX_STATE_WRITE_EOP_def = Define `
  RX_STATE_WRITE_EOP (nic : nic_state) =
  RX_STATE_WRITE_EOP_BUFFER_LENGTH nic \/
  RX_STATE_SET_EOP_EOP nic`;

val RX_STATE_WRITE_EOP_SOP_def = Define `
  RX_STATE_WRITE_EOP_SOP (nic : nic_state) =
  RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic`;

val RX_STATE_WRITE_EOP_OR_EOP_SOP_def = Define `
  RX_STATE_WRITE_EOP_OR_EOP_SOP nic =
  RX_STATE_WRITE_EOP nic \/
  RX_STATE_WRITE_EOP_SOP nic`;

val RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_def = Define `
  RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA (nic : nic_state) =
  RX_STATE_WRITE_SOP_BUFFER_OFFSET nic \/
  RX_STATE_WRITE_SOP_BUFFER_LENGTH nic \/
  RX_STATE_SET_SOP_SOP nic \/
  RX_STATE_WRITE_SOP_PASS_CRC nic \/
  RX_STATE_WRITE_SOP_LONG nic \/
  RX_STATE_WRITE_SOP_SHORT nic \/
  RX_STATE_WRITE_SOP_MAC_CTL nic \/
  RX_STATE_WRITE_SOP_PACKET_LENGTH nic`;

val RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def = Define `
  RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA nic =
  RX_STATE_WRITE_CURRENT_BD_PA nic \/
  RX_STATE_WRITE_EOP_OR_EOP_SOP nic \/
  RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA nic`;

val RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA_def = Define `
  RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA nic =
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic \/
  RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic`;

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_def = Define `
  RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic =
  RX_STATE_WRITE_EOP_OR_EOP_SOP nic \/
  RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA nic \/
  RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA nic`;

(* Not idle, fetch_next_bd, issue_next_memory_write_request nor write_cp. *)
val RX_STATE_WRITE_CPPI_RAM_def = Define `
  RX_STATE_WRITE_CPPI_RAM (nic : nic_state) =
  RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA nic \/
  RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA nic`;

(* Not idle, fetch_next_bd nor write_cp. *)
val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def = Define `
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM (nic : nic_state) =
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic \/
  RX_STATE_WRITE_CPPI_RAM nic`;

(* Not idle nor write_cp. *)
val RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def = Define `
  RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM (nic : nic_state) =
  RX_STATE_FETCH_NEXT_BD nic \/
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic \/
  RX_STATE_WRITE_CPPI_RAM nic`;

val _ = export_theory();
