open HolKernel Parse boolLib bossLib;
open helperTactics;
open txTheory;
open tx_state_definitionsTheory;
open tx_transition_definitionsTheory;
open tx_state_lemmasTheory;
open tx_bd_queueTheory;
open txLib;

val _ = new_theory "tx_transition_lemmas";

(* This theory contains definitions and lemmas related to the top-level tx
   transition function. *)

(* Generates terms of the following form:
   !nic env.
   TX_STATE_FETCH_NEXT_BD nic
   ==>
   (tx_transition env nic = (tx_1fetch_next_bd env nic, NONE))*)
fun generate_tx_state_imp_tx_transition_eq (tx_id : int) =
  let val ant = txLib.tx_id_to_tx_transition_state_application tx_id in
  let val leq = ``tx_transition env nic`` in
  let val req = txLib.tx_id_to_tx_transition_function_application tx_id in
  let val suc = mk_eq (leq, req) in
  let val imp = mk_imp (ant, suc) in
    list_mk_forall ([``nic : nic_state``, ``env : environment``], imp)
  end end end end end;

fun prove_tx_state_imp_tx_transition_eq (tx_id : int) = prove (
  generate_tx_state_imp_tx_transition_eq tx_id,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_transition_def, stateTheory.tx_abstract_state_case_def]);

(* Generates a theorem consisting of conjuncts of the following form:
   !nic env.
   TX_STATE_FETCH_NEXT_BD nic
   ==>
   (tx_transition env nic = (tx_1fetch_next_bd nic, NONE))*)
(* boolTheory.TRUTH is used as a dummy theorem for the states tx_idle and
   tx_process_memory_read_reply in order to make it possible to extract a
   conjunct by means of a state id and the function get_tx_conjunct. *)
val TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_lemmas = [
  boolTheory.TRUTH,
  prove_tx_state_imp_tx_transition_eq 1,
  prove_tx_state_imp_tx_transition_eq 2,
  boolTheory.TRUTH,
  prove_tx_state_imp_tx_transition_eq 4,
  prove_tx_state_imp_tx_transition_eq 5,
  prove_tx_state_imp_tx_transition_eq 6];

val TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas = save_thm (
  "TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas",
  LIST_CONJ TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_lemmas);

val TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REWRITE_TAC [TX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val TX_AUTONOMOUS_TRANSITION_IMP_TX_TRANSITION_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_IMP_TX_TRANSITION_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    ((nic',mr') = tx_transition env nic)``,
  REWRITE_TAC [TX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic``,
  REWRITE_TAC [TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    (nic' = tx_3process_memory_read_reply mr nic)``,
  REWRITE_TAC [TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_DEP_lemma = store_thm (
  "TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_DEP_lemma",
  ``!nic nic'.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    (nic'.tx.state = nic.tx.state)
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_DEP_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  REWRITE_TAC [TX_AUTONOMOUS_TRANSITION_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_AUTONOMOUS_TRANSITION_IMP_NOT_TX_STATE_IDLE_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_IMP_NOT_TX_STATE_IDLE_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    ~TX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  RW_ASM_TAC ``f nic`` TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_EQ_NOT_TX_STATE_IDLE_lemma THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_NOT_TX_STATE_IDLE_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_NOT_TX_STATE_IDLE_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    ~TX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  RW_ASM_TAC ``f nic`` TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_EQ_NOT_TX_STATE_IDLE_lemma THEN
  ASM_REWRITE_TAC []);





(* Lemmas used to prove that tx_transition preserves TD_INVARIANT. *)

val rw_nic =
  nic_rw_tactics.rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors];

val rw_tx =
  nic_rw_tactics.rw_state_tactic
  `t`
  [stateTheory.tx_state_fn_updates, combinTheory.K_THM, stateTheory.tx_state_accessors];

val rw_unfold_rw_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC txLib.tx_transition_defs THEN
  REWRITE_TAC [TX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true);

val rw_state_tactic =
  rw_nic THEN
  rw_tx THEN
  REWRITE_TAC [GSYM stateTheory.tx_abstract_state_distinct];

val tx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_TD_REGS_PRESERVED_lemma = store_thm (
  "tx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_TD_REGS_PRESERVED_lemma",
  ``!nic nic'.
    (nic' = tx_1fetch_next_bd nic)
    ==>
    ~TX_STATE_IDLE nic' \/ ((nic'.tx = nic.tx) /\ (nic'.tx = nic.tx) /\ (nic'.td = nic.td) /\ (nic'.regs = nic.regs))``,
  rw_unfold_rw_tactic THEN
  COND_CASES_TAC THENL
  [
   rw_nic
   ,
   ALL_TAC
  ] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  COND_CASES_TAC THENL
  [
   rw_nic
   ,
   ALL_TAC
  ] THEN
  COND_CASES_TAC THENL
  [
   rw_nic
   ,
   ALL_TAC
  ] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  rw_state_tactic);

val tx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "tx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic nic'.
    (nic' = tx_1fetch_next_bd nic) /\
    TX_STATE_FETCH_NEXT_BD nic
    ==>
    ~TX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_TD_REGS_PRESERVED_lemma)) THEN
  ASM_CASES_TAC ``~TX_STATE_IDLE nic'`` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~~P`` ``~P \/ Q`` THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``TX_STATE_FETCH_NEXT_BD nic`` TX_STATE_FETCH_NEXT_BD_def THEN
   ASM_REWRITE_TAC [TX_STATE_IDLE_def] THEN
   REWRITE_TAC [GSYM stateTheory.tx_abstract_state_distinct]
  ]);

val tx_2issue_next_memory_read_request_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "tx_2issue_next_memory_read_request_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = tx_2issue_next_memory_read_request nic)
    ==>
    ~TX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_2issue_next_memory_read_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  rw_unfold_rw_tactic THEN
  rw_state_tactic);

val tx_3process_memory_read_reply_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "tx_3process_memory_read_reply_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    ~TX_STATE_IDLE nic'``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_4post_process_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "tx_4post_process_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    ~TX_STATE_IDLE nic'``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_5clear_owner_and_hdp_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "tx_5clear_owner_and_hdp_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    ~TX_STATE_IDLE nic'``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_delta15_lemmas = LIST_CONJ [
  boolTheory.TRUTH,
  tx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_lemma,
  tx_2issue_next_memory_read_request_NEXT_STATE_NOT_IDLE_lemma,
  tx_3process_memory_read_reply_NEXT_STATE_NOT_IDLE_lemma,
  tx_4post_process_NEXT_STATE_NOT_IDLE_lemma,
  tx_5clear_owner_and_hdp_NEXT_STATE_NOT_IDLE_lemma,
  boolTheory.TRUTH];

fun get_tx_delta15 tx_state_id =
  txLib.get_tx_conjunct tx_delta15_lemmas tx_state_id;

fun get_tx_delta tx_state_id =
  txLib.get_tx_conjunct TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas tx_state_id;

val TX_AUTONOMOUS_TRANSITION_NEXT_TX_STATE_IDLE_NOT_CURRENT_TX_STATE_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_NEXT_TX_STATE_IDLE_NOT_CURRENT_TX_STATE_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    (TX_STATE_FETCH_NEXT_BD nic \/ TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic \/
     TX_STATE_POST_PROCESS nic \/ TX_STATE_CLEAR_OWNER_AND_HDP nic) /\
    TX_STATE_IDLE nic'
    ==>
    F``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_AUTONOMOUS_TRANSITION nic env nic' mr'`` TX_AUTONOMOUS_TRANSITION_def THEN
  SPLIT_ASM_TAC THEN
  (let fun tactic tx_state_id =
     ASSUME_TAC (UNDISCH (SPEC_ALL (get_tx_delta tx_state_id))) THEN
     ASM_RW_ASM_TAC ``tx_transition env nic = x`` ``y = tx_transition env nic`` THEN
     RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
     SPLIT_ASM_TAC THEN
     ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (get_tx_delta15 tx_state_id))) THEN
     ASM_RW_ASM_TAC ``~TX_STATE_IDLE nic'`` ``TX_STATE_IDLE nic'`` THEN
     ASM_REWRITE_TAC []
   in
   REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
     let val disj = (#1 o dest_disj o concl) thm in
     let val tx_state_id = txLib.tx_transition_state_application_to_tx_id disj
     in
       ASM_CASES_TAC disj THENL
       [
        tactic tx_state_id
        ,
        ASSUME_TAC thm THEN
        ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
       ]
     end end)) THEN
   (tactic 5)
   end));

val TX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_CURRENT_STATE_WRITE_CP_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_CURRENT_STATE_WRITE_CP_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_STATE_IDLE nic'
    ==>
    TX_STATE_WRITE_CP nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  RW_ASM_TAC ``TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`` TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_EQ_TX_STATE_CASESs_lemma THEN
  ASM_CASES_TAC ``TX_STATE_WRITE_CP nic`` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_AUTONOMOUS_TRANSITION_NEXT_TX_STATE_IDLE_NOT_CURRENT_TX_STATE_lemma)) THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val TX_AUTONOMOUS_TRANSITION_NEXT_TX_STATE_IDLE_IMP_PRESERVES_IT_TX_CURRENT_BD_PA_RX_RD_REGS_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_NEXT_TX_STATE_IDLE_IMP_PRESERVES_IT_TX_CURRENT_BD_PA_RX_RD_REGS_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_STATE_IDLE nic'
    ==>
    ((nic'.it = nic.it) /\
     (nic'.tx.current_bd_pa = nic.tx.current_bd_pa) /\
     (nic'.rx = nic.rx) /\
     (nic'.rd = nic.rd) /\
     (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_CURRENT_STATE_WRITE_CP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_TRANSITION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (txLib.get_tx_conjunct TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas 6))) THEN
  ASM_RW_ASM_TAC ``tx_transition env nic = x`` ``y = tx_transition env nic`` THEN
  RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  REWRITE_TAC [tx_6write_cp_def] THEN
  rw_nic THEN
  rw_tx THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors]);












val tx_1fetch_next_bd_PRESERVES_IT_RX_lemma = store_thm (
  "tx_1fetch_next_bd_PRESERVES_IT_RX_lemma",
  ``!nic nic'.
    (nic' = tx_1fetch_next_bd nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [tx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   rw_nic
   ,
   REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   COND_CASES_TAC THENL
   [
    rw_nic
    ,
    COND_CASES_TAC THENL
    [
     rw_nic
     ,
     rw_nic
    ]
   ]
  ]);

val tx_2issue_next_memory_read_request_PRESERVES_IT_RX_lemma = store_thm (
  "tx_2issue_next_memory_read_request_PRESERVES_IT_RX_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = tx_2issue_next_memory_read_request nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_2issue_next_memory_read_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  rw_nic);

val tx_3process_memory_read_reply_PRESERVES_IT_RX_lemma = store_thm (
  "tx_3process_memory_read_reply_PRESERVES_IT_RX_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_4post_process_PRESERVES_IT_RX_lemma = store_thm (
  "tx_4post_process_PRESERVES_IT_RX_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_5clear_owner_and_hdp_PRESERVES_IT_RX_lemma = store_thm (
  "tx_5clear_owner_and_hdp_PRESERVES_IT_RX_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_6write_cp_PRESERVES_IT_RX_lemma = store_thm (
  "tx_6write_cp_PRESERVES_IT_RX_lemma",
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val tx_delta_preserves_it_rx_lemmas = LIST_CONJ [
  boolTheory.TRUTH,
  tx_1fetch_next_bd_PRESERVES_IT_RX_lemma,
  tx_2issue_next_memory_read_request_PRESERVES_IT_RX_lemma,
  tx_3process_memory_read_reply_PRESERVES_IT_RX_lemma,
  tx_4post_process_PRESERVES_IT_RX_lemma,
  tx_5clear_owner_and_hdp_PRESERVES_IT_RX_lemma,
  tx_6write_cp_PRESERVES_IT_RX_lemma];

fun get_tx_delta_preserves_it_rx_lemma tx_state_id =
  txLib.get_tx_conjunct tx_delta_preserves_it_rx_lemmas tx_state_id;

val TX_AUTONOMOUS_TRANSITION_PRESERVES_IT_RX_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_PRESERVES_IT_RX_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  RW_ASM_TAC ``TX_AUTONOMOUS_TRANSITION nic env nic' mr'`` TX_AUTONOMOUS_TRANSITION_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`` TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_EQ_TX_STATE_CASESs_lemma THEN
  (let fun tactic tx_state_id =
     ASSUME_TAC (UNDISCH (SPEC_ALL (get_tx_delta tx_state_id))) THEN
     ASM_RW_ASM_TAC ``tx_transition env nic = x`` ``y = tx_transition env nic`` THEN
     RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
     SPLIT_ASM_TAC THEN
     ASSUME_TAC (UNDISCH (SPEC_ALL (get_tx_delta_preserves_it_rx_lemma tx_state_id))) THEN
     ASM_REWRITE_TAC []
   in
   REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
     let val disj = (#1 o dest_disj o concl) thm in
     let val tx_state_id = txLib.tx_transition_state_application_to_tx_id disj
     in
       ASM_CASES_TAC disj THENL
       [
        tactic tx_state_id
        ,
        ASSUME_TAC thm THEN
        ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
       ]
     end end)) THEN
   (tactic 6)
   end));

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_IT_RX_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_IT_RX_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC tx_3process_memory_read_reply_PRESERVES_IT_RX_lemma THEN
  EXISTS_TAC ``mr : memory_request`` THEN
  MATCH_MP_TAC TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma THEN
  ASM_REWRITE_TAC []);

val tx_3process_memory_read_reply_PRESERVES_DEAD_lemma = store_thm (
  "tx_3process_memory_read_reply_PRESERVES_DEAD_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    (nic'.dead = nic.dead)``,
  rw_unfold_rw_tactic THEN
  TRY (REPEAT COND_CASES_TAC THEN rw_state_tactic));

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_DEAD_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_DEAD_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC tx_3process_memory_read_reply_PRESERVES_DEAD_lemma THEN
  EXISTS_TAC ``mr : memory_request`` THEN
  MATCH_MP_TAC TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

