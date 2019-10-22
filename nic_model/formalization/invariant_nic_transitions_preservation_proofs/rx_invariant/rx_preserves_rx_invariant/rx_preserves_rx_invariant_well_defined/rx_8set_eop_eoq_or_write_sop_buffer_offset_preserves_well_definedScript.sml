open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_8set_eop_eoq_or_write_sop_buffer_offset_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_lemmasTheory;
open rx_state_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemmasTheory;

val _ = new_theory "rx_8set_eop_eoq_or_write_sop_buffer_offset_preserves_well_defined";

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_NOT_DEAD_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_NOT_DEAD_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_INVARIANT_NOT_DEAD nic
    ==>
    RX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NOT_DEAD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_BD_QUEUE_lemma)) THEN
  PAT_ASSUM ``BD_QUEUE q a (f a)`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM rx_8set_eop_eoq_or_write_sop_buffer_offset_NOT_MODIFIED_EQ_lemma] thm)) THEN
  REFLECT_ASM_TAC ``nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic`` THEN
  ASM_RW_ASM_TAC ``f a = r`` ``BD_QUEUE q (f a).rx.sop_bd_pa m`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic' : nic_state``, ``rx_bd_queue nic``] rx_bd_queueTheory.RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
  RW_ASM_TAC ``BD_QUEUE (rx_bd_queue nic') nic'.rx.sop_bd_pa nic'.regs.CPPI_RAM`` (GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma) THEN
  ASM_REWRITE_TAC []);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_STRUCTURE_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_BETWEEN_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_PRESERVES_BD_QUEUE_LOCATION_IMP_BD_QUEUE_STRUCTURE_PRESERVED_lemma THEN
  EXISTS_TAC ``rx_8set_eop_eoq_or_write_sop_buffer_offset_cppi_ram_write_step_bd_pas nic`` THEN
  REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma]);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def]);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_8set_eop_eoq_or_write_sop_buffer_offset`` THEN
  EXISTS_TAC ``rx_8set_eop_eoq_or_write_sop_buffer_offset_cppi_ram_write_step_bd_pas nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_SOP_BD_PA_lemma]);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_8set_eop_eoq_or_write_sop_buffer_offset`` THEN
  EXISTS_TAC ``rx_8set_eop_eoq_or_write_sop_buffer_offset_cppi_ram_write_step_bd_pas nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_SOP_BD_PA_lemma]);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_RX_SEEN_BDs_PRESERVES_WELL_DEFINED_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_8set_eop_eoq_or_write_sop_buffer_offset_cppi_ram_write_step_bd_pas nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic nic'.
    (nic' = rx_8set_eop_eoq_or_write_sop_buffer_offset nic) /\
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET nic /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    RX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_NOT_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_STRUCTURE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
