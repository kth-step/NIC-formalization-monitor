open HolKernel Parse boolLib bossLib;
open rd_state_definitionsTheory;

val _ = new_theory "rd_state_lemmas";

val NOT_RD_STATE_IDLE_IMP_RD_STATE_NOT_IDLE_lemma = store_thm (
  "NOT_RD_STATE_IDLE_IMP_RD_STATE_NOT_IDLE_lemma",
  ``!nic.
    ~RD_STATE_IDLE nic
    ==>
    RD_STATE_NOT_IDLE nic``,
  GEN_TAC THEN
  REWRITE_TAC [RD_STATE_NOT_IDLE_def] THEN
  REWRITE_TAC [RD_STATE_IDLE_def] THEN
  REWRITE_TAC [RD_STATE_SET_SOP_def] THEN
  REWRITE_TAC [RD_STATE_SET_EOP_def] THEN
  REWRITE_TAC [RD_STATE_SET_EOQ_def] THEN
  REWRITE_TAC [RD_STATE_SET_TD_def] THEN
  REWRITE_TAC [RD_STATE_CLEAR_OWNER_AND_HDP_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [stateTheory.rd_abstract_state_distinct]);

val RD_EQ_IMP_RD_STATE_EQ_lemma = store_thm (
  "RD_EQ_IMP_RD_STATE_EQ_lemma",
  ``!nic nic'.
    (nic'.rd = nic.rd)
    ==>
    (nic'.rd.state = nic.rd.state)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RD_STATE_IDLE_IMP_NOT_RD_STATE_WRITE_CP_lemma = store_thm (
  "RD_STATE_IDLE_IMP_NOT_RD_STATE_WRITE_CP_lemma",
  ``!nic.
    RD_STATE_IDLE nic
    ==>
    ~RD_STATE_WRITE_CP nic``,
  GEN_TAC THEN
  REWRITE_TAC [RD_STATE_IDLE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [stateTheory.rd_abstract_state_distinct]);

(*
  let val rd_state_applications =
    map (#1 o dest_eq o #2 o strip_forall o concl) rdLib.RD_STATE_defs in
  let val rd_state_applications_disjunction = list_mk_disj rd_state_applications in
  let val quantified_rd_state_cases =
    mk_forall (``nic : nic_state``, rd_state_applications_disjunction) in
    quantified_rd_state_cases
  end end end
*)
val RD_STATE_CASES_lemma = store_thm (
  "RD_STATE_CASES_lemma",
  ``!nic.
    RD_STATE_IDLE nic \/
    RD_STATE_SET_SOP nic \/
    RD_STATE_SET_EOP nic \/
    RD_STATE_SET_EOQ nic \/
    RD_STATE_SET_TD nic \/
    RD_STATE_CLEAR_OWNER_AND_HDP nic \/
    RD_STATE_WRITE_CP nic``,
  GEN_TAC THEN
  REWRITE_TAC rdLib.RD_STATE_defs THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC []);

val _ = export_theory();

