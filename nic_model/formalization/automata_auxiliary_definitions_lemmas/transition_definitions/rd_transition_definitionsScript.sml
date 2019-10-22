open HolKernel Parse boolLib bossLib;
open schedulerTheory;

val _ = new_theory "rd_transition_definitions";

val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def = Define `
  RD_STATE_AUTONOMOUS_TRANSITION_ENABLE nic = RD_ENABLE nic`;

val RD_AUTONOMOUS_TRANSITION_def = Define `
  RD_AUTONOMOUS_TRANSITION nic env nic' =
  (nic' = rd_transition env nic) /\
  RD_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`;

val NIC_DELTA_PRESERVES_RD_def = Define `
  NIC_DELTA_PRESERVES_RD (nic_delta : nic_delta_type) =
  !nic. (nic_delta nic).rd = nic.rd`;

val _ = export_theory();

