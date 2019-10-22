open HolKernel Parse boolLib bossLib;
open tx_state_definitionsTheory;
open rx_transition_definitionsTheory;
open CPPI_RAMTheory;
open bd_listTheory;
open rx_bd_queueTheory;
open tdTheory;

val _ = new_theory "tdInvariant";

val TD_STATE_WRITE_CPPI_RAM_def = Define `
  TD_STATE_WRITE_CPPI_RAM nic =
  TX_STATE_IDLE nic /\
  TD_WRITE_CURRENT_BD_PA nic`;

val TD_INVARIANT_def = Define `
  TD_INVARIANT nic =
  TD_STATE_WRITE_CPPI_RAM nic /\ RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
  ==>
  BD_IN_CPPI_RAM nic.tx.current_bd_pa /\
  BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)`;

val _ = export_theory();

