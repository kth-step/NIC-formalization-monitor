open HolKernel Parse boolLib bossLib;
open helperTactics;
open tdInvariantTheory;
open it_transition_lemmasTheory;

val _ = new_theory "it_preserves_td_invariant";

val IT_AUTONOMOUS_TRANSITION_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_PRESERVES_TD_INVARIANT_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TD_INVARIANT_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NOT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

