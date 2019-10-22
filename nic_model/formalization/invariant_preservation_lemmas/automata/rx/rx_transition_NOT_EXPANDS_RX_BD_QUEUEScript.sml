open HolKernel Parse boolLib bossLib;
open helperTactics;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedTheory;
open rx_write_defsTheory;
open rx_state_lemmasTheory;
open rx_transition_lemmasTheory;
open rx_transition_definitionsTheory;

val _ = new_theory "rx_transition_NOT_EXPANDS_RX_BD_QUEUE";

(* Lemma for transition functions 0, 1, 2 and 19. *)
val NIC_DELTA_PRESERVERS_RX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVERS_RX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_START_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_CLEARS_RX_SOP_BD_PA_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_CLEARS_RX_SOP_BD_PA_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_CLEARS_RX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CLEARS_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_START_BD_PA_POST_EQ_ZERO_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NEXT_RX_SOP_BD_PA_IN_RX_BD_QUEUE_SUB_INVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NEXT_RX_SOP_BD_PA_IN_RX_BD_QUEUE_SUB_INVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    MEM (nic_delta nic).rx.sop_bd_pa (rx_bd_queue nic)
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_def] THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_START_BD_PA_POST_IN_PRE_BD_QUEUE_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma, rx_bd_queue_def]);

(* Lemma for transition function 18 assigning nic.rx.sop_bd_pa. *)
val NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_CURRENT_BD_NDP_EQ_ZERO_OR_MEM_RX_BD_QUEUE_lemma)) THEN
  Cases_on `nic.rx.current_bd.ndp = 0w` THENL
  [
   MATCH_MP_TAC (SPEC_ALL (REWRITE_RULE [NIC_DELTA_CLEARS_RX_SOP_BD_PA_def] NIC_DELTA_CLEARS_RX_SOP_BD_PA_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   MATCH_MP_TAC (SPEC_ALL NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NEXT_RX_SOP_BD_PA_IN_RX_BD_QUEUE_SUB_INVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma) THEN
   ASM_REWRITE_TAC []
  ]);

(* Lemma for transition functions 3-16. *)
val NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_def] THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_IMP_NOT_EXPANDS_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma, rx_bd_queue_def]);

(* Lemma for transition function 17. *)
val NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def THEN
  Cases_on `NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*
Lemma for transition functions 0, 1, 2 and 19:
NIC_DELTA_PRESERVERS_RX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma

Lemma for transition functions 3-16:
NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma

Lemma for transition function 17:
NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma

Lemma for transition function 18 assigning nic.rx.sop_bd_pa:
NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma
*)
val RX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_lemmas =
  let fun create_list_with_lemmas (rx_id : int) =
    if 0 <= rx_id andalso rx_id <= 2 then
      NIC_DELTA_PRESERVERS_RX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma::create_list_with_lemmas (rx_id + 1)
    else if 3 <= rx_id andalso rx_id <= 16 then
      NIC_DELTA_WRITES_BD_QUEUE_FIELDs_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma::create_list_with_lemmas (rx_id + 1)
    else if rx_id = 17 then
      NIC_DELTA_WRITES_FIELDs_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma::create_list_with_lemmas (rx_id + 1)
    else if rx_id = 18 then
      NIC_DELTA_WRITES_BD_QUEUE_FIELDs_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_SUBINVARIANT_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma::create_list_with_lemmas (rx_id + 1)
    else if rx_id = 19 then
      [NIC_DELTA_PRESERVERS_RX_SOP_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_RX_BD_QUEUE_lemma]
    else
      raise Fail "create_list_with_lemmas: Not valid argument."
  in
    create_list_with_lemmas 0
  end;

fun rx_id_to_rx_subinvariant_imp_nic_delta_not_expands_rx_bd_queue (rx_id : int) =
  List.nth (RX_SUBINVARIANT_IMP_NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_lemmas, rx_id);

val NIC_DELTA_PRESERVES_RX_SOP_BD_PA_lemmas = [
  rx_0receive_new_frame_lemmasTheory.rx_0receive_new_frame_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_1fetch_next_bd_lemmasTheory.rx_1fetch_next_bd_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_3write_packet_error_lemmasTheory.rx_3write_packet_error_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_4write_rx_vlan_encap_lemmasTheory.rx_4write_rx_vlan_encap_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_5write_from_port_lemmasTheory.rx_5write_from_port_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_6write_eop_buffer_length_lemmasTheory.rx_6write_eop_buffer_length_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_7set_eop_eop_lemmasTheory.rx_7set_eop_eop_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_8set_eop_eoq_or_write_sop_buffer_offset_lemmasTheory.rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_9write_sop_buffer_offset_lemmasTheory.rx_9write_sop_buffer_offset_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_10write_sop_buffer_length_lemmasTheory.rx_10write_sop_buffer_length_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_11set_sop_sop_lemmasTheory.rx_11set_sop_sop_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_12write_sop_pass_crc_lemmasTheory.rx_12write_sop_pass_crc_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_13write_sop_long_lemmasTheory.rx_13write_sop_long_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_14write_sop_short_lemmasTheory.rx_14write_sop_short_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_15write_sop_mac_ctl_lemmasTheory.rx_15write_sop_mac_ctl_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_16write_sop_packet_length_lemmasTheory.rx_16write_sop_packet_length_PRESERVES_RX_SOP_BD_PA_lemma,
  rx_19write_cp_lemmasTheory.rx_19write_cp_PRESERVES_RX_SOP_BD_PA_lemma];

val NIC_DELTA_PRESERVES_CPPI_RAM_lemmas = [
  rx_0receive_new_frame_lemmasTheory.rx_0receive_new_frame_PRESERVES_CPPI_RAM_lemma,
  rx_1fetch_next_bd_lemmasTheory.rx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma,
  rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma,
  rx_19write_cp_lemmasTheory.rx_19write_cp_PRESERVES_CPPI_RAM_lemma];

(* Creates a goal of the form:
  ``!nic.
    RX_STATE... nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic`` *)
fun create_nic_delta_not_expands_rx_bd_queue_goal (rx_id : int) =
  let val state_predicate = rxLib.rx_id_to_rx_transition_state_application rx_id in
  let val subinvariant =
    ``RX_INVARIANT_BD_QUEUE_FINITE nic /\
      RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
      RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
      RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
      RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` in
  let val ant = mk_conj (state_predicate, subinvariant) in
  let val nic_delta = rxLib.rx_id_to_rx_transition_function rx_id in
  let val quantifiers = ``nic : nic_state``::(if rx_id = 2 then [] else (#2 o strip_comb) nic_delta) in
  let val args = [nic_delta, ``nic : nic_state``] in
  let val suc = list_mk_comb (``NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE``, args) in
  let val imp = mk_imp (ant, suc) in
  let val goal = list_mk_forall (quantifiers, imp) in
    goal
  end end end end end end end end end;

fun solve_nic_delta_not_expands_rx_bd_queue_goal0_1_2_19 (rx_id : int) =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC (rx_id_to_rx_subinvariant_imp_nic_delta_not_expands_rx_bd_queue rx_id) THEN
  REWRITE_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_lemmas THEN
  REWRITE_TAC NIC_DELTA_PRESERVES_CPPI_RAM_lemmas;

fun solve_nic_delta_not_expands_rx_bd_queue_goal3_through_16 (rx_id : int) =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC (rx_id_to_rx_subinvariant_imp_nic_delta_not_expands_rx_bd_queue rx_id) THEN
  EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (rxLib.get_rx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs rx_id)) THEN
  ASM_REWRITE_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_lemmas THEN
  MATCH_MP_TAC (rxLib.get_rx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas rx_id) THEN
  ASM_REWRITE_TAC [];

val solve_nic_delta_not_expands_rx_bd_queue_goal17 =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC (rx_id_to_rx_subinvariant_imp_nic_delta_not_expands_rx_bd_queue 17) THEN
  EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (rxLib.get_rx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs 17)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_lemmasTheory.rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma] THEN
  MATCH_MP_TAC (rxLib.get_rx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas 17) THEN
  ASM_REWRITE_TAC [];

val solve_nic_delta_not_expands_rx_bd_queue_goal18 =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC (rx_id_to_rx_subinvariant_imp_nic_delta_not_expands_rx_bd_queue 18) THEN
  EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (rxLib.get_rx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs 18)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_lemmasTheory.rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma] THEN
  MATCH_MP_TAC (rxLib.get_rx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas 18) THEN
  ASM_REWRITE_TAC [];

val NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_lemmas =
  let fun prove_nic_delta_not_expands_rx_bd_queue (rx_id : int) =
    let val goal = create_nic_delta_not_expands_rx_bd_queue_goal rx_id in
    let val tactic =
      if 0 <= rx_id andalso rx_id <= 2 then
        solve_nic_delta_not_expands_rx_bd_queue_goal0_1_2_19 rx_id
      else if 3 <= rx_id andalso rx_id <= 16 then
        solve_nic_delta_not_expands_rx_bd_queue_goal3_through_16 rx_id
      else if rx_id = 17 then
        solve_nic_delta_not_expands_rx_bd_queue_goal17
      else if rx_id = 18 then
        solve_nic_delta_not_expands_rx_bd_queue_goal18
      else if rx_id = 19 then
        solve_nic_delta_not_expands_rx_bd_queue_goal0_1_2_19 19
      else
        raise Fail "prove_nic_delta_not_expands_rx_bd_queue: Invalid argument."
    in
      if rx_id = 19 then
        [prove (goal, tactic)]
      else
        prove (goal, tactic)::prove_nic_delta_not_expands_rx_bd_queue (rx_id + 1)
    end end
  in
      prove_nic_delta_not_expands_rx_bd_queue 0
  end;

fun rx_id_to_nic_delta_not_expands_bd_queue_lemma (rx_id : int) =
  List.nth (NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_lemmas, rx_id);

val NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma = store_thm (
  "NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma",
  ``!nic_delta nic nic'.
    (nic' = nic_delta nic) /\
    NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE nic_delta nic
    ==>
    IN_LIST1_IMP_IN_LIST2 (rx_bd_queue nic') (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_bd_queue_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

fun prove_not_expands_rx_bd_queue (rx_id : int) =
  ASSUME_TAC ((UNDISCH o SPEC_ALL) (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id)) THEN
  ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``(nic', mr') = rx_transition env nic`` THEN
  ((RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
    PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) ORELSE
   (ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_FST_lemma)))) THEN
  MATCH_MP_TAC NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_IMP_POST_QUEUE_IN_PRE_QUEUE_lemma THEN
  EXISTS_TAC (rxLib.rx_id_to_rx_transition_function rx_id) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC (rx_id_to_nic_delta_not_expands_bd_queue_lemma rx_id) THEN
  ASM_REWRITE_TAC [];

val rx_transition_NOT_EXPANDS_RX_BD_QUEUE_lemma = store_thm (
  "rx_transition_NOT_EXPANDS_RX_BD_QUEUE_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    IN_LIST1_IMP_IN_LIST2 (rx_bd_queue nic') (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id left_disjunct in
      ASM_CASES_TAC left_disjunct THENL
      [
       prove_not_expands_rx_bd_queue rx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_not_expands_rx_bd_queue 19);

val _ = export_theory();

