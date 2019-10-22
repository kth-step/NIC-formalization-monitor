open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_transition_definitionsTheory;
open bd_queue_preservation_lemmasTheory;
open tx_invariant_well_defined_lemmasTheory;
open txInvariantWellDefinedTheory;
open tx_bd_queueTheory;
open tx_write_defsTheory;
open tx_transition_lemmasTheory;

val _ = new_theory "tx_transition_NOT_EXPANDS_TX_BD_QUEUE";

(* Lemma for transition functions 1, 2, 3 and 6. *)
val NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_PRESERVES_TX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_START_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(* Lemma for transition function 5. *)
val NIC_DELTA_CLEARS_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_CLEARS_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_CLEARS_TX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CLEARS_TX_SOP_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_START_BD_PA_POST_EQ_ZERO_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(* Lemma for transition function 4 when assigning sop_bd_pa being a member of the queue. *)
val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NEXT_TX_SOP_BD_PA_IN_TX_BD_QUEUE_SUB_INVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NEXT_TX_SOP_BD_PA_IN_TX_BD_QUEUE_SUB_INVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (tx_bd_queue nic) /\
    MEM (nic_delta nic).tx.sop_bd_pa (tx_bd_queue nic)
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_def] THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_START_BD_PA_POST_IN_PRE_BD_QUEUE_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASM_REWRITE_TAC [GSYM TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma, tx_bd_queue_def]);

(* Lemma for transition function 4 when only writing cppi_ram and not updating tx_sop_bd_pa. *)
val NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_TX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_TX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (tx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_TX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_def] THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_TX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def THEN
  ASM_REWRITE_TAC [GSYM TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma, tx_bd_queue_def]);

(* Lemma for transition function 4 when assigning sop_bd_pa. *)
val NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_STATE nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (tx_bd_queue nic) /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.tx.current_bd.ndp = 0w` THENL
  [
   MATCH_MP_TAC (SPEC_ALL (REWRITE_RULE [NIC_DELTA_CLEARS_TX_SOP_BD_PA_def] NIC_DELTA_CLEARS_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC (SPEC_ALL NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NEXT_TX_SOP_BD_PA_IN_TX_BD_QUEUE_SUB_INVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_lemmasTheory.TX_STATE_POST_PROCESS_SUBINVARIANT_NOT_ZERO_CURRENT_BD_NDP_IN_TX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(* Lemma for transition function 4. *)
val NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_STATE nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (tx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_def THEN
  Cases_on `NIC_DELTA_PRESERVES_TX_SOP_BD_PA nic_delta nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_TX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*
Lemma for transition functions 1, 2, 3, and 6:
NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma

Lemma for transition functions 4:
NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma

Lemma for transition function 5:
NIC_DELTA_CLEARS_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma
*)
val TX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_lemmas = [
  boolTheory.TRUTH,
  NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma,
  NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma,
  NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma,
  NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma,
  NIC_DELTA_CLEARS_TX_SOP_BD_PA_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma,
  NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_TX_BD_QUEUE_lemma];

val TX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas =
  LIST_CONJ TX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_lemmas;

val NIC_DELTA_PRESERVES_TX_SOP_BD_PA_lemmas = [
  boolTheory.TRUTH,
  tx_1fetch_next_bd_lemmasTheory.tx_1fetch_next_bd_PRESERVES_TX_SOP_BD_PA_lemma,
  tx_2issue_next_memory_read_request_lemmasTheory.tx_2issue_next_memory_read_request_PRESERVES_TX_SOP_BD_PA_lemma,
  tx_3process_memory_read_reply_lemmasTheory.tx_3process_memory_read_reply_PRESERVES_TX_SOP_BD_PA_lemma,
  boolTheory.TRUTH,
  boolTheory.TRUTH,
  tx_6write_cp_lemmasTheory.tx_6write_cp_PRESERVES_TX_SOP_BD_PA_lemma];

val NIC_DELTA_PRESERVES_TX_SOP_BD_PA_CONJ_lemmas =
  LIST_CONJ NIC_DELTA_PRESERVES_TX_SOP_BD_PA_lemmas;

val NIC_DELTA_PRESERVES_CPPI_RAM_lemmas = [
  boolTheory.TRUTH,
  tx_1fetch_next_bd_lemmasTheory.tx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma,
  tx_2issue_next_memory_read_request_lemmasTheory.tx_2issue_next_memory_read_request_PRESERVES_CPPI_RAM_lemma,
  tx_3process_memory_read_reply_lemmasTheory.tx_3process_memory_read_reply_PRESERVES_CPPI_RAM_lemma,
  boolTheory.TRUTH,
  boolTheory.TRUTH,
  tx_6write_cp_lemmasTheory.tx_6write_cp_PRESERVES_CPPI_RAM_lemma];

val NIC_DELTA_PRESERVES_CPPI_RAM_CONJ_lemmas =
  LIST_CONJ NIC_DELTA_PRESERVES_CPPI_RAM_lemmas;




(* Given an id of a tx state a goal of the following form is created:
  ``!nic.
    TX_STATE... nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_STATE nic
    ==>
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic`` *)
fun create_nic_delta_not_expands_tx_bd_queue_goal (tx_id : int) =
  let val state_predicate = txLib.tx_id_to_tx_transition_state_application tx_id in
  let val subinvariant =
    ``TX_INVARIANT_BD_QUEUE_FINITE nic /\
      TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
      TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
      TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
      TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
      TX_INVARIANT_CURRENT_BD_STATE nic`` in
  let val ant = mk_conj (state_predicate, subinvariant) in
  let val nic_delta = txLib.tx_id_to_tx_transition_function tx_id in
  let val quantifiers = ``nic : nic_state``::(if tx_id = 2 then [] else (#2 o strip_comb) nic_delta) in
  let val args = [nic_delta, ``nic : nic_state``] in
  let val suc = list_mk_comb (``NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE``, args) in
  let val imp = mk_imp (ant, suc) in
  let val goal = list_mk_forall (quantifiers, imp) in
    goal
  end end end end end end end end end;

fun solve_nic_delta_not_expands_tx_bd_queue_goal1_2_3_6 (tx_id : int) =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (txLib.get_tx_conjunct TX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas tx_id) THEN
  REWRITE_TAC NIC_DELTA_PRESERVES_TX_SOP_BD_PA_lemmas THEN
  REWRITE_TAC NIC_DELTA_PRESERVES_CPPI_RAM_lemmas;

val solve_nic_delta_not_expands_tx_bd_queue_goal4 =
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC (txLib.get_tx_conjunct TX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas 4) THEN
  EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (txLib.get_tx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs 4)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (txLib.get_tx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas 4))) THEN
  ASM_REWRITE_TAC [tx_4post_process_lemmasTheory.tx_4post_process_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_lemma];

val solve_nic_delta_not_expands_tx_bd_queue_goal5 =
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC (txLib.get_tx_conjunct TX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas 5) THEN
  REWRITE_TAC [tx_5clear_owner_and_hdp_lemmasTheory.tx_5clear_owner_and_hdp_CLEARS_TX_SOP_BD_PA_lemma];

val NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_lemmas =
  let fun prove_nic_delta_not_expands_tx_bd_queue (tx_id : int) =
    let val goal = create_nic_delta_not_expands_tx_bd_queue_goal tx_id in
    let val tactic =
      if 1 <= tx_id andalso tx_id <= 3 then
        solve_nic_delta_not_expands_tx_bd_queue_goal1_2_3_6 tx_id
      else if tx_id = 4 then
        solve_nic_delta_not_expands_tx_bd_queue_goal4
      else if tx_id = 5 then
        solve_nic_delta_not_expands_tx_bd_queue_goal5
      else if tx_id = 6 then
        solve_nic_delta_not_expands_tx_bd_queue_goal1_2_3_6 6
      else
        raise Fail "prove_nic_delta_not_expands_tx_bd_queue: Invalid argument."
    in
      if tx_id = 6 then
        [prove (goal, tactic)]
      else
        prove (goal, tactic)::prove_nic_delta_not_expands_tx_bd_queue (tx_id + 1)
    end end
  in
      boolTheory.TRUTH::prove_nic_delta_not_expands_tx_bd_queue 1
  end;

val NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas =
  LIST_CONJ NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_lemmas;

val NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma = store_thm (
  "NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma",
  ``!nic_delta nic nic'.
    (nic' = nic_delta nic) /\
    NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE nic_delta nic
    ==>
    IN_LIST1_IMP_IN_LIST2 (tx_bd_queue nic') (tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_bd_queue_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

fun prove_not_expands_tx_bd_queue (tx_id : int) =
  ASSUME_TAC ((UNDISCH o SPEC_ALL) (txLib.get_tx_conjunct TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas tx_id)) THEN
  ASM_RW_ASM_TAC ``tx_transition env nic = x`` ``(nic', mr') = tx_transition env nic`` THEN
  ((RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
    PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) ORELSE
   (ASSUME_TAC (UNDISCH (SPEC_ALL tx_2issue_next_memory_read_request_lemmasTheory.tx_2issue_next_memory_read_request_FST_lemma)))) THEN
  MATCH_MP_TAC NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma THEN
  EXISTS_TAC (txLib.tx_id_to_tx_transition_function tx_id) THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC (txLib.get_tx_conjunct NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas tx_id) THEN
  ASM_REWRITE_TAC [];

val tx_transition_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "tx_transition_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    IN_LIST1_IMP_IN_LIST2 (tx_bd_queue nic') (tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_state_lemmasTheory.TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm in
    let val tx_id = txLib.tx_transition_state_application_to_tx_id left_disjunct in
      ASM_CASES_TAC left_disjunct THENL
      [
       prove_not_expands_tx_bd_queue tx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_not_expands_tx_bd_queue 6);

val tx_memory_read_reply_NOT_EXPANDS_TX_BD_QUEUE_lemma = store_thm (
  "tx_memory_read_reply_NOT_EXPANDS_TX_BD_QUEUE_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    IN_LIST1_IMP_IN_LIST2 (tx_bd_queue nic') (tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma THEN
  EXISTS_TAC ``tx_3process_memory_read_reply mr`` THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC (txLib.get_tx_conjunct NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_CONJ_lemmas 3) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

