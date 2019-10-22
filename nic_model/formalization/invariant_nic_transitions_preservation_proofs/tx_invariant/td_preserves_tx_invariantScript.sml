open HolKernel Parse boolLib bossLib;
open td_transition_definitionsTheory;
open txInvariantTheory;
open td_transition_invariant_lemmasTheory;

val _ = new_theory "td_preserves_tx_invariant";

val TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_INVARIANT_lemma",
  ``!nic env nic' READABLE.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    TX_INVARIANT nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

