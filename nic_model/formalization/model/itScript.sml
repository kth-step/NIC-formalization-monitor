open HolKernel Parse boolLib bossLib;
open wordsTheory;
open stateTheory;

val _ = new_theory "it";

val it_1reset_def = Define `
  it_1reset (nic : nic_state) =
  nic with <|
    regs := nic.regs with CPDMA_SOFT_RESET := 0w;
    it := nic.it with state := it_initialize_hdp_cp
  |>`;

(*val it_transition_state_def = Define `
  it_transition_state it_reset nic = it_0reset nic`;
  it_transition_state it_reset nic = it_1reset nic`;
  it_transition_state it_reset nic = it_2reset nic`;
  it_transition_state it_reset nic = it_3reset nic`;*)

(* The autonomous transitions of the NIC model describing the initialization
   operations of the physical NIC. *)
val it_transition_def = Define `
  it_transition (nic : nic_state) =
  if nic.it.state = it_reset then
    it_1reset nic
  else
    nic with dead := T`;

val _ = export_theory();

