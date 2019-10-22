open HolKernel Parse boolLib bossLib;
open helperTactics;
open td_state_definitionsTheory;

val _ = new_theory "td_state_lemmas";

val NOT_TD_STATE_IDLE_IMP_TD_STATE_NOT_IDLE_lemma = store_thm (
  "NOT_TD_STATE_IDLE_IMP_TD_STATE_NOT_IDLE_lemma",
  ``!nic.
    ~TD_STATE_IDLE nic
    ==>
    TD_STATE_SET_EOQ nic \/
    TD_STATE_SET_TD nic \/
    TD_STATE_CLEAR_OWNER_AND_HDP nic \/
    TD_STATE_WRITE_CP nic``,
  GEN_TAC THEN
  REWRITE_TAC [TD_STATE_IDLE_def] THEN
  REWRITE_TAC [TD_STATE_SET_EOQ_def] THEN
  REWRITE_TAC [TD_STATE_SET_TD_def] THEN
  REWRITE_TAC [TD_STATE_CLEAR_OWNER_AND_HDP_def] THEN
  REWRITE_TAC [TD_STATE_WRITE_CP_def] THEN
  Cases_on `nic.td.state` THEN
  REWRITE_TAC [stateTheory.td_abstract_state_distinct]);

val TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TD_STATE_CASEs_lemma = store_thm (
  "TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TD_STATE_CASEs_lemma",
  ``!nic.
    TD_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
    ==>
    TD_STATE_SET_EOQ nic \/
    TD_STATE_SET_TD nic \/
    TD_STATE_CLEAR_OWNER_AND_HDP nic \/
    TD_STATE_WRITE_CP nic``,
  GEN_TAC THEN
  REWRITE_TAC [td_transition_definitionsTheory.TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.TD_ENABLE_def] THEN
  REWRITE_TAC [GSYM TD_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL NOT_TD_STATE_IDLE_IMP_TD_STATE_NOT_IDLE_lemma)) THEN
  ASM_REWRITE_TAC []);

val TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_NOT_TD_STATE_IDLE_lemma = store_thm (
  "TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_NOT_TD_STATE_IDLE_lemma",
  ``!nic.
    TD_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
    ==>
    ~TD_STATE_IDLE nic``,
  GEN_TAC THEN
  REWRITE_TAC [td_transition_definitionsTheory.TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.TD_ENABLE_def] THEN
  REWRITE_TAC [TD_STATE_IDLE_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val _ = export_theory();
