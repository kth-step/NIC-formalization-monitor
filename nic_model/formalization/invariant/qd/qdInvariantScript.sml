open HolKernel Parse boolLib bossLib;
open tx_transition_definitionsTheory
open rx_transition_definitionsTheory
open tx_bd_queueTheory;
open rx_bd_queueTheory;

val _ = new_theory "qdInvariant";

val QD_INVARIANT_def = Define `
  QD_INVARIANT nic =
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
  RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
  ==>
  BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)`;

val _ = export_theory();

