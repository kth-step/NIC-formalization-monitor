open HolKernel Parse boolLib bossLib;
open helperTactics;
open qdInvariantTheory;
open rd_transition_invariant_lemmasTheory;

val _ = new_theory "rd_preserves_qd_invariant";

val RD_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT nic
    ==>
    QD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_RD_INVARIANT_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

