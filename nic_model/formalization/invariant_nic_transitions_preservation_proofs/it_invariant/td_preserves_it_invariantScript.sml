open HolKernel Parse boolLib bossLib;
open helperTactics;
open itInvariantTheory;
open td_transition_definitionsTheory;
open it_state_definitionsTheory;
open td_transition_lemmasTheory;
open rx_state_definitionsTheory;

val _ = new_theory "td_preserves_it_invariant";

val TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE nic
    ==>
    IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE_def] THEN
  REWRITE_TAC [IT_STATE_INITIALIZED_def] THEN
  REWRITE_TAC [tx_state_definitionsTheory.TX_STATE_IDLE_def] THEN
  REWRITE_TAC [rx_state_definitionsTheory.RX_STATE_IDLE_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_STATE_RX_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``nic'.it = nic.it`` ``nic'.it.state <> it_initialized`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT nic
    ==>
    IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT_def] THEN
  REWRITE_TAC [IT_STATE_RESET_def] THEN
  REWRITE_TAC [RX0_HDP_INITIALIZED_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_STATE_RX_lemma)) THEN
  SPLIT_ASM_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``nic'.it = nic.it`` ``nic'.it.state = it_reset`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_RW_ASM_TAC ``nic'.it = nic.it`` ``nic'.it.rx0_hdp_initialized`` THEN
  ASM_RW_ASM_TAC ``nic.it.rx0_hdp_initialized`` ``~nic.it.rx0_hdp_initialized`` THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY nic
    ==>
    IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY_def] THEN
  REWRITE_TAC [IT_STATE_INITIALIZE_HDP_CP_def, RX0_HDP_INITIALIZED_def] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_STATE_RX_lemma)) THEN
  SPLIT_ASM_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``nic'.it = nic.it`` ``nic'.it.state = it_initialize_hdp_cp`` THEN
  ASM_RW_ASM_TAC ``nic'.it = nic.it`` ``nic'.it.rx0_hdp_initialized`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    IT_INVARIANT nic
    ==>
    IT_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
