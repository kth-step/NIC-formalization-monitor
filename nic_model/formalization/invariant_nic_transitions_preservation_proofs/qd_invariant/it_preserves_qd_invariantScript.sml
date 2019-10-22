open HolKernel Parse boolLib bossLib;
open qdInvariantTheory;
open it_transition_lemmasTheory;

val _ = new_theory "it_preserves_qd_invariant";

val IT_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    QD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NOT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

