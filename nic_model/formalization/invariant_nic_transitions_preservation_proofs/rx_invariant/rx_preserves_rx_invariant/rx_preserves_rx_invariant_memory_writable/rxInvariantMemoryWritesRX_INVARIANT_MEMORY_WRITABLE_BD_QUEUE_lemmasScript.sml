open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantMemoryWritesTheory;
open bdTheory;
open bd_listTheory;
open rx_bd_queueTheory;
open rxInvariantWellDefinedLemmasTheory;
open rx_write_defsTheory;

val _ = new_theory "rxInvariantMemoryWritesRX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemmas";

(*
NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic \/
NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE nic_delta nic
==>{NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma, NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma}
NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic


NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
==>NIC_DELTA_RX_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma
EQ_BDs (rx_unseen_bd_queue nic) M M'


P (rx_unseen_bd_queue nic) M /\
EQ_BDs (rx_unseen_bd_queue nic) M M'
==>NIC_DELTA_EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma
P (rx_unseen_bd_queue nic) M'


P (rx_unseen_bd_queue nic) M' /\
NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic
==>NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma
P (rx_unseen_bd_queue (nic_delta nic)) M'

This gives:
P (rx_unseen_bd_queue nic) M /\
NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE /\
NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic /\
==>{NIC_DELTA_RX_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
    NIC_DELTA_EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma,
    NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma}
P (rx_unseen_bd_queue (nic_delta nic)) M'
*)

val BD_EQ_PRESERVES_BD_ADDRESSES_WRITABLE_MEMORY_lemma = store_thm (
  "BD_EQ_PRESERVES_BD_ADDRESSES_WRITABLE_MEMORY_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM' WRITABLE.
    BD_ADDRESSES_WRITABLE_MEMORY bd_pa CPPI_RAM WRITABLE /\
    BD_EQ bd_pa CPPI_RAM CPPI_RAM'
    ==>
    BD_ADDRESSES_WRITABLE_MEMORY bd_pa CPPI_RAM' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_ADDRESSES_WRITABLE_MEMORY_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (GSYM (UNDISCH (SPEC_ALL BD_EQ_IMP_rx_read_bd_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!q CPPI_RAM CPPI_RAM' WRITABLE.
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE q CPPI_RAM WRITABLE /\
    EQ_BDs q CPPI_RAM CPPI_RAM'
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE q CPPI_RAM' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_def] THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC BD_EQ_PRESERVES_BD_ADDRESSES_WRITABLE_MEMORY_lemma THEN
  EXISTS_TAC ``CPPI_RAM : cppi_ram_type`` THEN
  CONJ_TAC THENL
  [
   PAT_ASSUM ``!x. P ==> BD_ADDRESSES_WRITABLE_MEMORY x m WRITABLE`` (fn thm => MATCH_MP_TAC thm) THEN
   ASM_REWRITE_TAC []
   ,
   PAT_ASSUM ``!e. MEM e q ==> BD_EQ e CPPI_RAM CPPI_RAM'`` (fn thm => MATCH_MP_TAC thm) THEN
   ASM_REWRITE_TAC []
  ]);

val NIC_DELTA_EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!nic_delta nic WRITABLE.
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE /\
    EQ_BDs (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) (nic_delta nic).regs.CPPI_RAM WRITABLE``,
  REWRITE_TAC [EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma]);




val IN_LIST1_IMP_IN_LIST2_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "IN_LIST1_IMP_IN_LIST2_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!q q' CPPI_RAM WRITABLE.
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE q CPPI_RAM WRITABLE /\
    IN_LIST1_IMP_IN_LIST2 q' q
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE q' CPPI_RAM WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  MATCH_MP_TAC IN_LIST1_AND_IN_LIST1_IMP_IN_LIST2_IMP_IN_LIST2_lemma THEN
  EXISTS_TAC ``q' : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!nic_delta nic WRITABLE.
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE
      (rx_unseen_bd_queue nic) (nic_delta nic).regs.CPPI_RAM WRITABLE /\
    NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE
      (rx_unseen_bd_queue (nic_delta nic)) (nic_delta nic).regs.CPPI_RAM WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_unseen_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);



val NIC_DELTA_WRITES_RX_SEEN_BD_QUEUE_EXPANDS_NOT_UNSEEN_BD_QUEUE_IMP_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_RX_SEEN_BD_QUEUE_EXPANDS_NOT_UNSEEN_BD_QUEUE_IMP_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas WRITABLE.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue (nic_delta nic)) (nic_delta nic).regs.CPPI_RAM WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_EQ_BDs_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_RX_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);








val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemmas = [
  rx_0receive_new_frame_lemmasTheory.rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_1fetch_next_bd_lemmasTheory.rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_3write_packet_error_lemmasTheory.RX_STATE_WRITE_PACKET_ERROR_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_4write_rx_vlan_encap_lemmasTheory.RX_STATE_WRITE_RX_VLAN_ENCAP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_5write_from_port_lemmasTheory.RX_STATE_WRITE_FROM_PORT_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_6write_eop_buffer_length_lemmasTheory.RX_STATE_WRITE_EOP_BUFFER_LENGTH_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_7set_eop_eop_lemmasTheory.RX_STATE_SET_EOP_EOP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_8set_eop_eoq_or_write_sop_buffer_offset_lemmasTheory.RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_9write_sop_buffer_offset_lemmasTheory.RX_STATE_WRITE_SOP_BUFFER_OFFSET_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_10write_sop_buffer_length_lemmasTheory.RX_STATE_WRITE_SOP_BUFFER_LENGTH_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_11set_sop_sop_lemmasTheory.RX_STATE_SET_SOP_SOP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_12write_sop_pass_crc_lemmasTheory.RX_STATE_WRITE_SOP_PASS_CRC_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_13write_sop_long_lemmasTheory.RX_STATE_WRITE_SOP_LONG_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_14write_sop_short_lemmasTheory.RX_STATE_WRITE_SOP_SHORT_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_15write_sop_mac_ctl_lemmasTheory.RX_STATE_WRITE_SOP_MAC_CTL_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_16write_sop_packet_length_lemmasTheory.RX_STATE_WRITE_SOP_PACKET_LENGTH_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_lemmasTheory.RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_18clear_sop_owner_and_hdp_lemmasTheory.RX_STATE_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma,
  rx_19write_cp_lemmasTheory.rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma];

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_CONJ_lemmas =
  LIST_CONJ NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemmas;

val NIC_DELTA_SHRINKS_OR_PRESERVES_RX_UNSEEN_BD_QUEUE_lemmas = [
  rx_0receive_new_frame_lemmasTheory.rx_0receive_new_frame_SUBINVARIANT_IMP_SHRINKS_UNSEEN_BD_QUEUE_lemma,
  rx_1fetch_next_bd_lemmasTheory.rx_1fetch_next_bd_SUBINVARIANT_IMP_SHRINKS_UNSEEN_BD_QUEUE_lemma,
  rx_2issue_next_memory_write_request_lemmasTheory.RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_3write_packet_error_lemmasTheory.RX_STATE_WRITE_PACKET_ERROR_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_4write_rx_vlan_encap_lemmasTheory.RX_STATE_WRITE_RX_VLAN_ENCAP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_5write_from_port_lemmasTheory.RX_STATE_WRITE_FROM_PORT_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_6write_eop_buffer_length_lemmasTheory.RX_STATE_WRITE_EOP_BUFFER_LENGTH_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_7set_eop_eop_lemmasTheory.RX_STATE_SET_EOP_EOP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_8set_eop_eoq_or_write_sop_buffer_offset_lemmasTheory.RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_9write_sop_buffer_offset_lemmasTheory.RX_STATE_WRITE_SOP_BUFFER_OFFSET_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_10write_sop_buffer_length_lemmasTheory.RX_STATE_WRITE_SOP_BUFFER_LENGTH_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_11set_sop_sop_lemmasTheory.RX_STATE_SET_SOP_SOP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_12write_sop_pass_crc_lemmasTheory.RX_STATE_WRITE_SOP_PASS_CRC_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_13write_sop_long_lemmasTheory.RX_STATE_WRITE_SOP_LONG_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_14write_sop_short_lemmasTheory.RX_STATE_WRITE_SOP_SHORT_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_15write_sop_mac_ctl_lemmasTheory.RX_STATE_WRITE_SOP_MAC_CTL_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_16write_sop_packet_length_lemmasTheory.RX_STATE_WRITE_SOP_PACKET_LENGTH_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_lemmasTheory.RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_18clear_sop_owner_and_hdp_lemmasTheory.RX_STATE_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma,
  rx_19write_cp_lemmasTheory.RX_STATE_WRITE_CP_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma];




(* Given a theorem of the form
   |- !nic a0 ... an-1. P ==> Q transition nic

   a term of the folloing form is returned
   ``!nic a0 ... an-1. P ==> NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE transition nic`` *)
fun mk_nic_delta_not_expands_rx_unseen_bd_queue_goal lemma =
  let val (quantifiers, imp) = (strip_forall o concl) lemma in
  let val (ant, suc) = dest_imp imp in
  let val suc_args = (#2 o strip_comb) suc in
  let val new_function = (#1 o strip_comb o #1 o dest_eq o #2 o strip_forall o concl) NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_def in
  let val new_suc = list_mk_comb (new_function, suc_args) in
  let val new_imp = mk_imp (ant, new_suc) in
  let val goal = list_mk_forall (quantifiers, new_imp) in
  let val tactic =
    REPEAT GEN_TAC THEN
    DISCH_TAC THEN
    SPLIT_ASM_TAC THEN
    MATCH_MP_TAC NIC_DELTA_SHRINKS_OR_PRESERVES_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma THEN
    ASSUME_TAC (UNDISCH (SPEC_ALL lemma)) THEN
    ASM_REWRITE_TAC []
  in
    prove (goal, tactic)
  end end end end end end end end;

val NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemmas = map mk_nic_delta_not_expands_rx_unseen_bd_queue_goal NIC_DELTA_SHRINKS_OR_PRESERVES_RX_UNSEEN_BD_QUEUE_lemmas;

val NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_CONJ_lemmas =
  LIST_CONJ NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemmas;

(* Given an rx_id a term of the following form is generated:
   !nic a0 WRITABLE.
   RX_STATE... nic /\
   RX_INVARIANT_BD_QUEUE_FINITE nic /\
   RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
   RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
   RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
   RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
   RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
   RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
   RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE``;
   ==>
   RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue (nic_delta nic a0)) (nic_delta nic a0).regs.CPPI_RAM WRITABLE *)
fun create_memory_writable_bd_queue_preservation_goal rx_id =
  let val left = rxLib.rx_id_to_rx_transition_state_application rx_id in
  let val right =
    ``RX_INVARIANT_BD_QUEUE_FINITE nic /\
      RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
      RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
      RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
      RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
      RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
      RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
      RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE`` in
  let val ant = mk_conj (left, right) in
  let val P = (#1 o strip_comb o #1 o dest_eq o #2 o strip_forall o concl) RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_def in
  let val nic_delta_args = rxLib.rx_id_to_nic_delta_application rx_id in
  let val rx_unseen_bd_queue_nic_delta_args = mk_comb (``rx_unseen_bd_queue``, nic_delta_args) in
  let val nic_delta_args_regs = mk_comb (``nic_state_regs``, nic_delta_args) in
  let val nic_delta_args_regs_cppi_ram = mk_comb (``nic_regs_CPPI_RAM``, nic_delta_args_regs) in
  let val writable = ``WRITABLE : bd_pa_type -> bool`` in
  let val suc = list_mk_comb (P, [rx_unseen_bd_queue_nic_delta_args, nic_delta_args_regs_cppi_ram, writable]) in
  let val imp = mk_imp (ant, suc) in
  let val quantifiers = 
    if rx_id = 2 then
      [``nic : nic_state``]
    else
      (#2 o strip_comb o rxLib.rx_id_to_nic_delta_application) rx_id in
  let val goal = list_mk_forall ((List.rev quantifiers) @ [writable], imp) in
    goal
  end end end end end end end end end end end end end;

fun solve_memory_writable_bd_queue_preservation_goal rx_id =
  let fun match_or_rewrite_tactic rx_id =
    let val lemma = rxLib.get_rx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_CONJ_lemmas rx_id in
    let val is_imp = (is_imp o #2 o strip_forall o concl) lemma in
      if is_imp then
        MATCH_MP_TAC lemma THEN
        ASM_REWRITE_TAC []
      else
        REWRITE_TAC [lemma]
    end end
  in
  let val tactic =
    REPEAT GEN_TAC THEN
    DISCH_TAC THEN
    MATCH_MP_TAC NIC_DELTA_WRITES_RX_SEEN_BD_QUEUE_EXPANDS_NOT_UNSEEN_BD_QUEUE_IMP_MEMORY_WRITABLE_BD_QUEUE_lemma THEN
    EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (rxLib.get_rx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs rx_id)) THEN
    ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [
     match_or_rewrite_tactic rx_id
     ,
     MATCH_MP_TAC (rxLib.get_rx_conjunct NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_CONJ_lemmas rx_id) THEN
     ASM_REWRITE_TAC []
    ]
  in
    tactic
  end end;

(* Theorems of the form:
  |- ∀nic v WRITABLE.
     RX_STATE_WRITE_CP nic ∧
     RX_INVARIANT_BD_QUEUE_FINITE nic ∧
     RX_INVARIANT_BD_QUEUE_STRUCTURE nic ∧
     RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic ∧
     RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) ∧
     RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) ∧
     RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM ∧
     RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic ∧
     RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE
     ⇒
     RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE
       (rx_unseen_bd_queue (rx_19write_cp env nic))
       (rx_19write_cp env nic).regs.CPPI_RAM
       WRITABLE:
*)
val NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemmas =
  let fun prove_goal rx_id =
    let val goal = create_memory_writable_bd_queue_preservation_goal rx_id in
      prove (goal, solve_memory_writable_bd_queue_preservation_goal rx_id)
    end
  in
  let fun prove_goal_rec 19 = [prove_goal 19]
	| prove_goal_rec rx_id = prove_goal rx_id::prove_goal_rec (rx_id + 1)
  in
    prove_goal_rec 0
  end end;

val NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_CONJ_lemmas =
  LIST_CONJ NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemmas;




(* Transforms a lemma of the form:
   !nic env WRITABLE.
   RX_STATE...
   ...
   ==>
   RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue ...
   to

   1. a term:
   ``RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic'...`` 

   2. and a string of the name of the transition function
   "nic_delta"
   *)
fun create_nic_delta_nic_memory_writable_bd_queue_preservation_goal lemma =
  let val (quantifiers, imp) = (strip_forall o concl) lemma in
  let val (ant, suc) = dest_imp imp in
  let val right_conj = ant in
  let val rx_id = (rxLib.rx_transition_state_application_to_rx_id o #1 o dest_conj) ant in
  let val rhs = rxLib.rx_id_to_nic_delta_application rx_id in
  let val lhs = ``nic' : nic_state`` in
  let val eq = mk_eq (lhs, rhs) in
  let val left_conj = eq in
  let val new_ant = mk_conj (left_conj, right_conj) in
  let val new_suc = ``RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE`` in
  let val new_imp = mk_imp (new_ant, new_suc) in
  let val new_quantifiers = hd quantifiers::(hd o tl) quantifiers::lhs::(tl o tl) quantifiers in
  let val goal = list_mk_forall (new_quantifiers, new_imp) in
    goal
  end end end end end end end end end end end end end;

fun solve_nic_delta_nic_memory_writable_bd_queue_preservation_goal lemma =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC lemma THEN
  TRY (EXISTS_TAC ``env : environment``) THEN
  ASM_REWRITE_TAC [];

(* Theorems of the form:
  |- ∀nic env nic' WRITABLE.
     (nic' = rx_19write_cp env nic) ∧
     RX_STATE_WRITE_CP nic ∧
     RX_INVARIANT_BD_QUEUE_FINITE nic ∧
     RX_INVARIANT_BD_QUEUE_STRUCTURE nic ∧
     RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic ∧
     RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) ∧
     RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) ∧
     RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM ∧
     RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic ∧
     RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE
     ⇒
     RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE
*)
val NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemmas =
  let val create_goal = create_nic_delta_nic_memory_writable_bd_queue_preservation_goal in
  let val solve_goal = solve_nic_delta_nic_memory_writable_bd_queue_preservation_goal in
  let fun get_lemma (rx_id : int) = rxLib.get_rx_conjunct NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_CONJ_lemmas rx_id in
  let fun prove_lemma (rx_id : int) = let val lemma = get_lemma rx_id in prove (create_goal lemma, solve_goal lemma) end in
  let fun prove_rec 19 = [prove_lemma 19]
	| prove_rec rx_id = prove_lemma rx_id::prove_rec (rx_id + 1)
  in
    prove_rec 0
  end end end end end;

val NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_CONJ_lemmas = save_thm (
  "NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_CONJ_lemmas",
  LIST_CONJ NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemmas);

val _ = export_theory();

