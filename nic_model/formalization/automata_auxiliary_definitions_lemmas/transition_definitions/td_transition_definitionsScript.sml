open HolKernel Parse boolLib bossLib;
open schedulerTheory;
open tdTheory;

val _ = new_theory "td_transition_definitions";

val TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def = Define `
  TD_STATE_AUTONOMOUS_TRANSITION_ENABLE nic = TD_ENABLE nic`;

val TD_AUTONOMOUS_TRANSITION_def = Define `
  TD_AUTONOMOUS_TRANSITION nic env nic' =
  (nic' = td_transition env nic) /\
  TD_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`;

val _ = export_theory();

