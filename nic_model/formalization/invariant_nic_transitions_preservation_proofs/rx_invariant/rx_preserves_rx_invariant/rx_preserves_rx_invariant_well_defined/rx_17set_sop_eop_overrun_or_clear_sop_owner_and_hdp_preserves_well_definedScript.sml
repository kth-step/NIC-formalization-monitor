open HolKernel Parse boolLib bossLib;
open helperTactics;
open rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rx_state_lemmasTheory;
open rx_18clear_sop_owner_and_hdp_lemmasTheory;

val _ = new_theory "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_preserves_well_defined";

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_NOT_DEAD_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_NOT_DEAD_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_INVARIANT_NOT_DEAD nic
    ==>
    RX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NOT_DEAD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
   ASM_RW_ASM_TAC ``f a1 a2 = g a`` ``nic' = f a1 a2`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_STRUCTURE_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
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
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
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
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
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
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    RX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_NOT_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_STRUCTURE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
