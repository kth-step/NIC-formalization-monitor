open HolKernel Parse boolLib bossLib;
open rx_state_definitionsTheory;
open rdTheory;
open tx_transition_definitionsTheory;
open CPPI_RAMTheory;
open bd_listTheory;
open tx_bd_queueTheory;
open rd_state_definitionsTheory;
open rx_transition_definitionsTheory;

val _ = new_theory "rdInvariant";

val RD_STATE_WRITE_CPPI_RAM_def = Define `
  RD_STATE_WRITE_CPPI_RAM nic =
  RX_STATE_IDLE nic /\
  RD_WRITE_CURRENT_BD_PA nic`;

val RD_INVARIANT_CURRENT_BD_PA_def = Define `
  RD_INVARIANT_CURRENT_BD_PA nic =
  RD_STATE_WRITE_CPPI_RAM nic /\
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic
  ==>
  BD_IN_CPPI_RAM nic.rx.current_bd_pa /\
  BD_NOT_OVERLAP_BDs nic.rx.current_bd_pa (tx_bd_queue nic)`;

(* Implies that when reception teardown is complete, the reception automaton
   cannot perform a transition and its invariant therefore holds vacously. *)
val RD_INVARIANT_RD_CLEARS_BD_QUEUE_def = Define `
  RD_INVARIANT_RD_CLEARS_BD_QUEUE nic =
  RD_STATE_WRITE_CP nic
  ==>
  RX_BD_QUEUE_EMPTY nic`;

(* This invariant allows the reception automaton to update nic.rx.sop_bd_pa to
   a non-zero value, without contradicting the previous invariant
   RD_INVARIANT_RD_CLEARS_BD_QUEUE. *)
val RD_INVARIANT_RX_ADVANCES_BD_QUEUE_def = Define `
  RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic =
  RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
  ==>
  ~RD_STATE_WRITE_CP nic`;

val RD_INVARIANT_def = Define `
  RD_INVARIANT nic =
  RD_INVARIANT_CURRENT_BD_PA nic /\
  RD_INVARIANT_RD_CLEARS_BD_QUEUE nic /\
  RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic`;

val _ = export_theory();

