open HolKernel Parse boolLib bossLib;
open helperTactics;
open txInvariantTheory;
open it_transition_lemmasTheory;

val _ = new_theory "it_preserves_tx_invariant";

val IT_AUTONOMOUS_TRANSITION_PRESERVES_TX_INVARIANT_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_PRESERVES_TX_INVARIANT_lemma",
  ``!nic nic' READABLE.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    TX_INVARIANT nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NOT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

