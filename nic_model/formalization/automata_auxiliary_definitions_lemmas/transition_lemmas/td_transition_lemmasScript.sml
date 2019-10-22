open HolKernel Parse boolLib bossLib;
open helperTactics;
open tdTheory;
open td_transition_definitionsTheory;

val _ = new_theory "td_transition_lemmas";

val TD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic' = td_transition env nic)``,
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val nic_rw =
  (nic_rw_tactics.rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors]) THEN
  (nic_rw_tactics.rw_state_tactic
  `t`
  [stateTheory.tx_state_fn_updates, combinTheory.K_THM, stateTheory.tx_state_accessors]);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_STATE_RX_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_STATE_RX_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.it = nic.it) /\
    (nic'.tx.state = nic.tx.state) /\
    (nic'.rx = nic.rx)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  REWRITE_TAC [td_transition_def] THEN
  Cases_on `nic.td.state` THEN
  REWRITE_TAC [stateTheory.td_abstract_state_case_def] THEN
  REWRITE_TAC [td_1set_eoq_def, td_2set_td_def, td_3clear_owner_and_hdp_def, td_4write_cp_def] THEN
  ((nic_rw THEN NO_TAC) ORELSE
   (COND_CASES_TAC THENL
    [
     nic_rw THEN NO_TAC
     ,
     COND_CASES_TAC THEN (nic_rw THEN NO_TAC)
    ]) ORELSE
   (COND_CASES_TAC THEN (nic_rw THEN NO_TAC))
  ));

val TD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.TD_ENABLE_def] THEN
  REWRITE_TAC [td_transition_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `nic.td.state` THEN
  REWRITE_TAC [stateTheory.td_abstract_state_case_def] THEN
  TRY (RW_ASM_TAC ``td_idle <> td_idle`` boolTheory.TRUTH THEN UNDISCH_TAC ``F`` THEN REWRITE_TAC []) THEN
  REWRITE_TAC [td_1set_eoq_def, td_2set_td_def] THEN
  REWRITE_TAC [td_3clear_owner_and_hdp_def, td_4write_cp_def] THEN
  REPEAT (
   COND_CASES_TAC THENL
   [
    nic_rw
    ,
    ALL_TAC
   ] ORELSE
   nic_rw));

val _ = export_theory();

