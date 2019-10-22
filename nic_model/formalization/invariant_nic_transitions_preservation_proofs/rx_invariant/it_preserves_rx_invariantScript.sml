open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantTheory;
open it_transition_lemmasTheory;

val _ = new_theory "it_preserves_rx_invariant";

val IT_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma",
  ``!nic nic' WRITABLE.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NOT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

