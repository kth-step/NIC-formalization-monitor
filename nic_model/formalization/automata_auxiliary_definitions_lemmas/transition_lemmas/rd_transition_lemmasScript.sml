open HolKernel Parse boolLib bossLib;
open helperTactics;
open rdTheory;
open rd_transition_definitionsTheory;
open rx_state_definitionsTheory;
open rd_state_definitionsTheory;

val _ = new_theory "rd_transition_lemmas";

(* Generates terms of the following form:
   !nic env.
   RD_STATE_IDLE nic
   ==>
   (rd_transition env nic = rd_0idle env nic)*)
fun generate_rd_state_imp_rd_transition_eq (rd_id : int) =
  let val ant = rdLib.rd_id_to_rd_transition_state_application rd_id in
  let val leq = ``rd_transition env nic`` in
  let val req = rdLib.rd_id_to_rd_transition_function_application rd_id in
  let val suc = mk_eq (leq, req) in
  let val imp = mk_imp (ant, suc) in
  mk_forall (``nic : nic_state``, mk_forall (``env : environment``, imp))
  end end end end end;

fun prove_rd_state_imp_rd_transition_eq (rd_id : int) = prove (
  generate_rd_state_imp_rd_transition_eq rd_id,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rdLib.RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws] THEN
  REWRITE_TAC rdLib.RD_STATE_defs THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rd_transition_def, rd_transition_case_def, stateTheory.rd_abstract_state_case_def]);

fun prove_rd_state_imp_rd_transition_eqs 6    = [prove_rd_state_imp_rd_transition_eq 6]
  | prove_rd_state_imp_rd_transition_eqs rd_id = (prove_rd_state_imp_rd_transition_eq rd_id)::(prove_rd_state_imp_rd_transition_eqs (rd_id + 1));

val RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_lemmas = prove_rd_state_imp_rd_transition_eqs 0;

val RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_CONJ_lemmas = save_thm (
  "RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_CONJ_lemmas",
  LIST_CONJ RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_lemmas);

val RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic' = rd_transition env nic)``,
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.RD_ENABLE_def] THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_IMP_RD_STATE_NOT_IDLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_RD_STATE_NOT_IDLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RD_STATE_NOT_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.RD_ENABLE_def] THEN
  REWRITE_TAC [GSYM RD_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rd_state_lemmasTheory.NOT_RD_STATE_IDLE_IMP_RD_STATE_NOT_IDLE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_IMP_RD_ENABLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_RD_ENABLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RD_ENABLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val nic_rw =
  (nic_rw_tactics.rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors]) THEN
  (nic_rw_tactics.rw_state_tactic
  `r`
  [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val RD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_RX_STATE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_IT_TX_RX_STATE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.rx.state = nic.rx.state)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC [rd_0idle_def, rd_1set_sop_def] THEN
  REWRITE_TAC [rd_2set_eop_def, rd_3set_eoq_def] THEN
  REWRITE_TAC [rd_4set_td_def, rd_5clear_owner_and_hdp_def] THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  REPEAT (
   COND_CASES_TAC THENL
   [
    nic_rw
    ,
    ALL_TAC
   ] ORELSE
   nic_rw));

val RD_AUTONOMOUS_TRANSITION_PRESERVES_OR_CLEARS_RX_SOP_BD_PA_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_OR_CLEARS_RX_SOP_BD_PA_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) \/
    (nic'.rx.sop_bd_pa = 0w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC [rd_0idle_def, rd_1set_sop_def] THEN
  REWRITE_TAC [rd_2set_eop_def, rd_3set_eoq_def] THEN
  REWRITE_TAC [rd_4set_td_def, rd_5clear_owner_and_hdp_def] THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  REPEAT (
   COND_CASES_TAC THENL
   [
    nic_rw
    ,
    ALL_TAC
   ] ORELSE
   nic_rw));

val RD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.RD_ENABLE_def] THEN
  REWRITE_TAC [rd_transition_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `nic.rd.state` THEN
  TRY (RW_ASM_TAC ``rd_idle <> rd_idle`` boolTheory.TRUTH THEN UNDISCH_TAC ``F`` THEN REWRITE_TAC []) THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC [rd_0idle_def, rd_1set_sop_def] THEN
  REWRITE_TAC [rd_2set_eop_def, rd_3set_eoq_def] THEN
  REWRITE_TAC [rd_4set_td_def, rd_5clear_owner_and_hdp_def] THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  REPEAT (
   COND_CASES_TAC THENL
   [
    nic_rw
    ,
    ALL_TAC
   ] ORELSE
   nic_rw));

val _ = export_theory();

