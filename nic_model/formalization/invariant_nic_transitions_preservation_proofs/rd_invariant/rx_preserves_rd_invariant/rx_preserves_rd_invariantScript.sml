open HolKernel Parse boolLib bossLib;
open helperTactics;
open rdInvariantTheory;
open rx_transition_preserves_rd_invariant_current_bd_paTheory;
open rx_transition_preserves_rd_invariant_rd_clears_bd_queueTheory;

val _ = new_theory "rx_preserves_rd_invariant";

val RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_lemma",
  ``!nic env nic' mr' WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_INVARIANT nic WRITABLE /\
    RD_INVARIANT nic /\
    QD_INVARIANT nic
    ==>
    RD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_CURRENT_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

