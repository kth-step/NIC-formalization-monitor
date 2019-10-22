open HolKernel Parse boolLib bossLib;
open helperTactics;
open rdInvariantTheory;
open td_transition_invariant_lemmasTheory;
open rd_state_definitionsTheory;
open rx_transition_definitionsTheory;
open rx_state_definitionsTheory;

val _ = new_theory "td_preserves_rd_invariant";

val TD_AUTONOMOUS_TRANSITION_IMP_NEXT_RD_INVARIANT_CURRENT_BD_PA_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_NEXT_RD_INVARIANT_CURRENT_BD_PA_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RD_INVARIANT_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma)) THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  ASM_RW_ASM_TAC ``(nic' : nic_state).rd = nic.rd`` ``nic'.rd.state = rd_write_cp`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic
    ==>
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RX_ADVANCES_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma)) THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``~RD_STATE_WRITE_CP nic`` RD_STATE_WRITE_CP_def THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT nic
    ==>
    RD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_NEXT_RD_INVARIANT_CURRENT_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

