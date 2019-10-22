open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open rx_state_definitionsTheory;
open rx_1fetch_next_bd_lemmasTheory;
open rx_0receive_new_frame_lemmasTheory;
open rxInvariantMemoryWritesTheory;
open rx_2issue_next_memory_write_request_lemmasTheory;

val _ = new_theory "rxInvariantMemoryWritesRX_INVARIANTs_CURRENT_BUFFER_WRITABLE_NEXT_MEMORY_WRITE_PA_lemmas";

(* Prove Invariant nic
   (<==> RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST (nic_delta nic) ==> P (nic_delta nic))

   Proof plan for each nic_delta (3-19):
   1. NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST nic_delta nic
      (<==> ~RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST (nic_delta nic)).
   2. NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST nic_delta nic
      ==>
      Invariant (nic_delta nic)
   3. Invariant (nic_delta nic), by 1. and 2.
   4. nic' = nic_delta nic ==> Invariant nic', by 3.
*)

val NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_def = Define `
  NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST (nic_delta : nic_delta_type) nic =
  ~RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST (nic_delta nic)`;

val rx_transition3_19_defs = List.drop (rxLib.rx_transition_defs, 3);

(* Given |- !nic a0 ... an-1. transition nic a0 an-1 = ...
   a term of the following form is returned:
   !nic. NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST (transition a0 ... an-1) nic
*)
fun create_nic_delta_next_state_neq_issue_memory_request_goal transition_def =
  let val (quantifiers, definition) = (strip_forall o concl) transition_def in
  let val nic_delta = (#1 o dest_comb o #1 o dest_eq) definition in
  let val pred = ``NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST`` in
  let val nic = ``nic : nic_state`` in
  let val goal = list_mk_forall (quantifiers, mk_comb (mk_comb (pred, nic_delta), nic)) in
    goal
  end end end end end;

(* Tactic solving goals of the form
   !nic a0 ... an-1. NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST transition nic. *)
fun solve_nic_delta_next_state_neq_issue_memory_request_goal (asl, con) =
  (REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  REWRITE_TAC rx_transition3_19_defs THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  (REPEAT COND_CASES_TAC) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
  (fn (asl, con) =>
   let val eq_tm = (dest_eq o dest_neg) con in
   let val leq = #1 eq_tm in
   let val req = #2 eq_tm in
   let fun get_id f_tm = (#2 o dest_comb) f_tm in
   let val id1 = get_id leq in
   let val id2 = get_id req in
   let val EQ_lemmas = [DECIDE ``^id1 < 20``, DECIDE ``^id2 < 20``] in
   let val RW_lemma = REWRITE_RULE EQ_lemmas (SPECL [id1, id2] stateTheory.num2rx_abstract_state_11) in
   REWRITE_TAC [RW_lemma] (asl, con)
   end end end end end end end end) THEN
  DECIDE_TAC) (asl, con);

(* Theorems of the form
   !nic a0 ... an-1. NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST transition nic
   for each transition function of the reception automaton with ID 3-19. *)
val NIC_DELTAs_3_19_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_lemmas =
  let val create_goal = create_nic_delta_next_state_neq_issue_memory_request_goal in
  let val solve_goal = solve_nic_delta_next_state_neq_issue_memory_request_goal in
  map (fn transition_def => (prove (create_goal transition_def, solve_goal))) rx_transition3_19_defs
  end end;

(* Given a definition of the form: |- !nic b0 ... bn-1. RX_INVARIANT nic b0 ... bn-1 = ...
   Returns: ``RX_INVARIANT`` *)
val invariant_def_to_invariant_term = #1 o strip_comb o #1 o dest_eq o #2 o strip_forall o concl;

(* Given a definition of the form: |- !nic b0 ... bn-1. RX_INVARIANT nic b0 ... bn-1 = ...
   Returns: [``nic``, ``b0``, ..., ``bn-1``] *)
val invariant_def_to_invariant_args = #1 o strip_forall o concl;

(* Given:
   -|- !nic b0 ... bm-1. RX_INVARIANT nic b0 ... bm-1 = ...
   -|- !nic a0 ... an-1. transition a0 ... an-1 nic = ...
   Returns:
   ``!nic a0 ... an-1 nic' b0 ... bm-1.
     (nic' = transition a0 ... an-1 nic)
     ==>
     RX_INVARIANT nic' b0 ... bm-1`` *)
fun mk_nic_delta_invariant_imp_goal invariant_def transition_def =
  let val nic_delta_args = (List.rev o #1 o strip_forall o concl) transition_def in
  let val nic_delta_application = (#1 o dest_eq o #2 o strip_forall o concl) transition_def in
  let val ant = mk_eq (``nic' : nic_state``, nic_delta_application) in
  let val inv = invariant_def_to_invariant_term invariant_def in
  let val inv_args = (tl o invariant_def_to_invariant_args) invariant_def in
  let val suc = list_mk_comb (inv, ``nic' : nic_state``::inv_args) in
  let val imp = mk_imp (ant, suc) in
  let val goal = list_mk_forall (nic_delta_args @ [``nic' : nic_state``] @ inv_args, imp) in
    goal
  end end end end end end end end;

(* Tactic solving goals of the form
   !nic a0 ... an-1 nic' b0 ... bm-1.
   nic' = transition a0 ... an-1 nic
   ==>
   RX_INVARIANT nic' b0 ... bm-1

   given a lemma of the form
   !nic_delta nic b0 ... bm-1.
   NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST nic_delta nic
   ==>
   RX_INVARIANT (nic_delta nic) b0 .. bm-1
*)
fun solve_nic_delta_imp_invariant_with_imp_lemma_goal lemma =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC lemma THEN
  REWRITE_TAC NIC_DELTAs_3_19_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_lemmas;

(* Tactic solving goals of the form
   !nic a0 ... an-1 nic' b0 ... bm-1.
   nic' = transition a0 ... an-1 nic
   ==>
   RX_INVARIANT nic' b0 ... bm-1

   given lemmas of the form
   !nic .
   RX_INVARIANT (transition a0 ... an-1 nic) b0 ... bm-1 *)
fun solve_nic_delta_imp_invariant_with_lemma lemmas =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC lemmas;

(***********************************************)
(**Start of Lemmas for CURRENT_BUFFER_WRITABLE**)
(***********************************************)

val rx_0receive_new_frame_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma",
  ``!nic env nic' WRITABLE.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE
    ==>
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_IMP_CURRENT_BUFFER_WRITABLE_lemma THEN
  EXISTS_TAC ``receive_frame env.rx.received_frame nic`` THEN
  (fn (asl, con) =>
   let val nic_term = ``nic : nic_state`` in
   let val env_term = ``env : environment`` in
   let val nic'_term = ``receive_frame env.rx.received_frame nic`` in
   let val specs = SPECL [nic_term, env_term, nic'_term] in
   let val writable_term = ``WRITABLE : bd_pa_type -> bool`` in
   let val rw = UNDISCH o (REWRITE_RULE []) in
     (ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma)) THEN
     ASSUME_TAC (rw (SPECL [nic_term, env_term, nic'_term, writable_term] receive_frame_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma))) (asl, con)
   end end end end end end) THEN
  ASM_REWRITE_TAC [GSYM rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma]);

val rx_1fetch_next_bd_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma",
  ``!nic nic' WRITABLE.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE
    ==>
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPEC_ALL rx_1fetch_next_bd_IMP_CURRENT_BUFFER_WRITABLE_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma",
  ``!nic mr' nic' WRITABLE.
    ((nic',mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic WRITABLE
    ==>
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_CURRENT_BUFFER_WRITABLE_lemma = store_thm (
  "NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_CURRENT_BUFFER_WRITABLE_lemma",
  ``!nic_delta nic WRITABLE.
    NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST nic_delta nic
    ==>
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE (nic_delta nic) WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_def] THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

(* Theorems of the form
   !nic a0 ... an-1 WRITABLE. RX_INVARIANT... (transition a0 ... an-1 nic) WRITABLE *)
val NIC_DELTA3_19_PRESERVES_CURRENT_BUFFER_WRITABLE_lemmas =
  let val create_goal = mk_nic_delta_invariant_imp_goal RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def in
  let val solve_goal = solve_nic_delta_imp_invariant_with_imp_lemma_goal NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_CURRENT_BUFFER_WRITABLE_lemma in
    map (fn transition_def => prove (create_goal transition_def, solve_goal)) rx_transition3_19_defs end end;

(* Theorems of the form (nic' = nic_delta nic ==> RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE. *)
val NIC_DELTA_PRESERVES_CURRENT_BUFFER_WRITABLE_lemmas = 
  rx_0receive_new_frame_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma::
  rx_1fetch_next_bd_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma::
  rx_2issue_next_memory_write_request_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma::
  NIC_DELTA3_19_PRESERVES_CURRENT_BUFFER_WRITABLE_lemmas;

val NIC_DELTA_PRESERVES_CURRENT_BUFFER_WRITABLE_CONJ_lemmas = save_thm (
  "NIC_DELTA_PRESERVES_CURRENT_BUFFER_WRITABLE_CONJ_lemmas",
  LIST_CONJ NIC_DELTA_PRESERVES_CURRENT_BUFFER_WRITABLE_lemmas);

(*********************************************)
(**End of Lemmas for CURRENT_BUFFER_WRITABLE**)
(*********************************************)

(*******************************************************************************)
(**Start of Lemmas for NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES**)
(*******************************************************************************)

val rx_0receive_new_frame_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma THEN
  EXISTS_TAC ``receive_frame env.rx.received_frame nic`` THEN
  (fn (asl, con) =>
   let val nic_term = ``nic : nic_state`` in
   let val env_term = ``env : environment`` in
   let val nic'_term = ``receive_frame env.rx.received_frame nic`` in
   let val specs = SPECL [nic_term, env_term, nic'_term] in
   let val rw = UNDISCH o (REWRITE_RULE []) in
     (ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma))) (asl, con)
   end end end end end) THEN
  ASM_REWRITE_TAC [GSYM rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma]);

val rx_1fetch_next_bd_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma",
  ``!nic mr' nic'.
    ((nic',mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` ``P ==> Q`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma = store_thm (
  "NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma",
  ``!nic_delta nic.
    NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST nic_delta nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_def] THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

(* Theorems of the form
   !nic a0 ... an-1 nic'.
   nic' = nic_delta env nic
   ==>
   RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'. *)
val NIC_DELTA3_19_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemmas =
  let val create_goal = mk_nic_delta_invariant_imp_goal RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def in
  let val solve_goal = solve_nic_delta_imp_invariant_with_imp_lemma_goal NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma in
    map (fn transition_def => prove (create_goal transition_def, solve_goal)) rx_transition3_19_defs end end;

val NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemmas =
  rx_0receive_new_frame_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma::
  rx_1fetch_next_bd_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma::
  rx_2issue_next_memory_write_request_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma::
  NIC_DELTA3_19_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemmas;

val NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_CONJ_lemmas = save_thm (
  "NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_CONJ_lemmas",
  LIST_CONJ NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemmas);

(*****************************************************************************)
(**End of Lemmas for NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES**)
(*****************************************************************************)

(******************************************************)
(**Start of Lemmas for NEXT_MEMORY_WRITE_PA_IN_BUFFER**)
(******************************************************)

val rx_0receive_new_frame_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma THEN
  EXISTS_TAC ``receive_frame env.rx.received_frame nic`` THEN
  (fn (asl, con) =>
   let val nic_term = ``nic : nic_state`` in
   let val env_term = ``env : environment`` in
   let val nic'_term = ``receive_frame env.rx.received_frame nic`` in
   let val specs = SPECL [nic_term, env_term, nic'_term] in
   let val rw = UNDISCH o (REWRITE_RULE []) in
     (ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma))) (asl, con)
   end end end end end) THEN
  ASM_REWRITE_TAC [GSYM rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma]);

val rx_1fetch_next_bd_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic /\
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STORE_MORE_BYTES nic.rx` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic_delta nic.
    NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST nic_delta nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_def] THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

(* Theorems of the form
   !nic a0 ... an-1 nic'.
   nic' = transition a0 ... an-1 nic
   ==>
   RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic' *)
val NIC_DELTA3_19_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemmas =
  let val create_goal = mk_nic_delta_invariant_imp_goal RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def in
  let val solve_goal = solve_nic_delta_imp_invariant_with_imp_lemma_goal NIC_DELTA_NEXT_STATE_NEQ_ISSUE_MEMORY_REQUEST_IMP_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma in
  map (fn transition_def => (prove (create_goal transition_def, solve_goal))) rx_transition3_19_defs
  end end;

val NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemmas =
  rx_0receive_new_frame_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma::
  rx_1fetch_next_bd_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma::
  rx_2issue_next_memory_write_request_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma::
  NIC_DELTA3_19_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemmas;

val NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_CONJ_lemmas = save_thm (
  "NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_CONJ_lemmas",
  LIST_CONJ NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemmas);

(****************************************************)
(**End of Lemmas for NEXT_MEMORY_WRITE_PA_IN_BUFFER**)
(****************************************************)

val _ = export_theory();

