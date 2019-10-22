open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "tx_state_definitions";

val TX_STATE_IDLE_def = Define `
  TX_STATE_IDLE nic = (nic.tx.state = tx_idle)`;

val TX_STATE_FETCH_NEXT_BD_def = Define `
  TX_STATE_FETCH_NEXT_BD nic = (nic.tx.state = tx_fetch_next_bd)`;

val TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def = Define `
  TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic = (nic.tx.state = tx_issue_next_memory_read_request)`;

val TX_STATE_PROCESS_MEMORY_READ_REPLY_def = Define `
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic = (nic.tx.state = tx_process_memory_read_reply)`;

val TX_STATE_POST_PROCESS_def = Define `
  TX_STATE_POST_PROCESS nic = (nic.tx.state = tx_post_process)`;

val TX_STATE_CLEAR_OWNER_AND_HDP_def = Define `
  TX_STATE_CLEAR_OWNER_AND_HDP nic = (nic.tx.state = tx_clear_owner_and_hdp)`;

val TX_STATE_WRITE_CP_def = Define `
  TX_STATE_WRITE_CP nic = (nic.tx.state = tx_write_cp)`;

val TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_def = Define`
  TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP (nic : nic_state) =
  TX_STATE_IDLE nic \/
  TX_STATE_FETCH_NEXT_BD nic \/
  TX_STATE_WRITE_CP nic`;

val TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_def = Define `
  TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE (nic : nic_state) =
  TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic \/
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic \/
  TX_STATE_POST_PROCESS nic \/
  TX_STATE_CLEAR_OWNER_AND_HDP nic`;

(*
 * In which states the transmission queue is not empty.
 *)
val TX_STATE_NOT_BD_QUEUE_EMPTY_def = Define `
  TX_STATE_NOT_BD_QUEUE_EMPTY nic =
  TX_STATE_FETCH_NEXT_BD nic \/
  TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic \/
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic \/
  TX_STATE_POST_PROCESS nic \/
  TX_STATE_CLEAR_OWNER_AND_HDP nic \/
  (TX_STATE_WRITE_CP nic /\ nic.tx.sop_bd_pa <> 0w)`;

val _ = export_theory();

