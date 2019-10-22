open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open rx_state_lemmasTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_FINITE_lemmas";

(***************************************************************************************)
(*Start of lemmas for transition functions not writing CPPI_RAM nor updating sop_bd_pa:
  rxTheory.rx_0receive_new_frame_def
  rxTheory.rx_1fetch_next_bd_def
  rxTheory.rx_2issue_next_memory_write_request_def
  rxTheory.rx_19write_cp_def
*)
(***************************************************************************************)

val RX_INVARIANT_BD_QUEUE_FINITE_DEP_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_FINITE_DEP_lemma",
  ``!nic nic'.
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta.
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
   REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
   DISCH_TAC THEN
   MATCH_MP_TAC RX_INVARIANT_BD_QUEUE_FINITE_DEP_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   ASM_REWRITE_TAC []);

(***************************************************************************************)
(*End of lemmas for transition functions not writing buffer descriptors nor updating
  sop_bd_pa*)
(***************************************************************************************)

(***************************************************************************************)
(*Start of lemmas for transition functions writing CPPI_RAM and not updating sop_bd_pa:
  rxTheory.rx_3write_packet_error_def
  rxTheory.rx_4write_rx_vlan_encap_def
  rxTheory.rx_5write_from_port_def
  rxTheory.rx_6write_eop_buffer_length_def
  rxTheory.rx_7set_eop_eop_def
  rxTheory.rx_8set_eop_eoq_or_write_sop_buffer_offset_def
  rxTheory.rx_9write_sop_buffer_offset_def
  rxTheory.rx_10write_sop_buffer_length_def
  rxTheory.rx_11set_sop_sop_def
  rxTheory.rx_12write_sop_pass_crc_def
  rxTheory.rx_13write_sop_long_def
  rxTheory.rx_14write_sop_short_def
  rxTheory.rx_15write_sop_mac_ctl_def
  rxTheory.rx_16write_sop_packet_length_def*)
(****************************************************************************************)

val RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic_delta : nic_delta_type``, ``nic : nic_state``, ``rx_bd_queue nic``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);



(***Start of lemmas for writing current_bd_pa***)

val RX_STATE_WRITE_CURRENT_BD_PA_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_WRITE_CURRENT_BD_PA_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA nic cppi_ram_write_step_bd_pas /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def]);

(***End of lemmas for writing current_bd_pa***)

(***Start of lemmas for writing eop_bd_pa***)

val RX_STATE_WRITE_EOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_WRITE_EOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_EOP_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def]);

(***End of lemmas for writing eop_bd_pa***)

(***Start of lemmas for writing eop_bd_pa and sop_bd_pa***)

val RX_STATE_WRITE_EOP_SOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_WRITE_EOP_SOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_EOP_SOP_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def]);

val RX_STATE_SET_SOP_EOP_OVERRUN_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def]);

(***End of lemmas for writing eop_bd_pa and sop_bd_pa***)

(***Start of lemmas for writing sop_bd_pa***)

val RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_PRESERVED_SOP_BD_PA_IMP_NEXT_RX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def]);

(***End of lemmas for writing sop_bd_pa***)

val RX_STATE_WRITE_CPPI_RAM_NOT_SOP_BD_PA_SOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_NOT_SOP_BD_PA_SOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   MATCH_MP_TAC RX_STATE_WRITE_CURRENT_BD_PA_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma THEN
   EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   MATCH_MP_TAC RX_STATE_WRITE_EOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma THEN
   EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   MATCH_MP_TAC RX_STATE_WRITE_EOP_SOP_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma THEN
   EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   MATCH_MP_TAC RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma THEN
   EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_NIC_DELTA_PRESERVES_RX_SOP_BD_PA_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);






(**********************************************************************************************)
(*End of lemmas for transition functions writing buffer descriptors and not updating sop_bd_pa*)
(**********************************************************************************************)


(********************************************************************************************)
(*Start of lemmas for transition functions writing CPPI_RAM and updating sop_bd_pa:
  rxTheory.rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def
  rxTheory.rx_18clear_sop_owner_and_hdp_def*)
(********************************************************************************************)

val RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_IMP_NEXT_RX_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_IMP_NEXT_RX_BD_QUEUE_lemma",
  ``!nic nic' cppi_ram_write_step_bd_pas.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic) /\
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    MEM nic.rx.current_bd_pa (rx_bd_queue nic) /\
    (nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) /\
    (nic'.rx.sop_bd_pa = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = cppi_ram_write nic.regs.CPPI_RAM cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE (rx_bd_queue nic') nic'.rx.sop_bd_pa nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_IN_CPPI_RAM_NON_OVERLAPPING_WRITTEN_PRESERVED_NDPs_MEM_Q_IMP_BD_QUEUE_NEXT_MEM_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  EXISTS_TAC ``nic.rx.sop_bd_pa`` THEN
  EXISTS_TAC ``nic'.regs.CPPI_RAM`` THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas q`` CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def THEN
  RW_ASM_TAC ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas`` PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_UPDATES_SOP_BD_PA_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_UPDATES_SOP_BD_PA_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic' cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas /\
    (nic'.rx.sop_bd_pa = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = cppi_ram_write nic.regs.CPPI_RAM cppi_ram_write_step_bd_pas)
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic ==> Q`` THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P \/ Q ==> R`` THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  MATCH_MP_TAC RX_BD_QUEUE_NON_OVERLAPPING_IN_CPPI_RAM_WRITTEN_PRESERVED_NDPs_IMP_NEXT_RX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_NIC_DELTA_UPDATES_SOP_BD_PA_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_NIC_DELTA_UPDATES_SOP_BD_PA_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_SETS_RX_SOP_BD_PA_TO_NDP nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [NIC_DELTA_SETS_RX_SOP_BD_PA_TO_NDP_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_UPDATES_SOP_BD_PA_PRESERVES_BD_QUEUE_FINITE_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

(******************************************************************************************)
(*End of lemmas for transition functions writing buffer descriptors and updating sop_bd_pa*)
(******************************************************************************************)

val _ = export_theory();

