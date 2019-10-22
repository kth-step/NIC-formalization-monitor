open HolKernel Parse boolLib bossLib;
open schedulerTheory;

val _ = new_theory "it_transition_definitions";

val IT_STATE_AUTONOMOUS_TRANSITION_ENABLE_def = Define `
  IT_STATE_AUTONOMOUS_TRANSITION_ENABLE nic = IT_ENABLE nic`;

val IT_AUTONOMOUS_TRANSITION_def = Define `
  IT_AUTONOMOUS_TRANSITION nic nic' =
  (nic' = it_transition nic) /\
  IT_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`;

val NIC_DELTA_PRESERVES_IT_def = Define `
  NIC_DELTA_PRESERVES_IT (nic_delta : nic_delta_type) =
  !nic. (nic_delta nic).it = nic.it`;

val _ = export_theory();

