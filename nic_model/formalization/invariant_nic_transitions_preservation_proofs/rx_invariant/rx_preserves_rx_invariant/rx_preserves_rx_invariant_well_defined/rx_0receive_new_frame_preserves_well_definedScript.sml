open HolKernel Parse boolLib bossLib;
open helperTactics;
open rx_0receive_new_frame_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rx_1fetch_next_bd_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_FINITE_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemmasTheory;

val _ = new_theory "rx_0receive_new_frame_preserves_well_defined";

val rx_0receive_new_frame_PRESERVES_NOT_DEAD_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_NOT_DEAD_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_NOT_DEAD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_dead_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_NOT_DEAD nic`` RX_INVARIANT_NOT_DEAD_def THEN
  ASM_REWRITE_TAC [RX_INVARIANT_NOT_DEAD_def]);

val rx_0receive_new_frame_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC rx_1fetch_next_bd_NOT_MODIFIED_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (RX_INVARIANT_BD_QUEUE_FINITE_DEP_lemma))) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_PRESERVES_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_BD_QUEUE_STRUCTURE_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_NOT_DEAD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic'' : nic_state``] receive_frame_PRESERVES_RX_SUBINVARIANT_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPECL [``nic'' : nic_state``, ``nic' : nic_state``] rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_PRESERVES_BD_QUEUE_STRUCTURE_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic''`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def]);

val rx_0receive_new_frame_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_0receive_new_frame env`` THEN
  ASM_REWRITE_TAC [rx_0receive_new_frame_PRESERVES_RX_SOP_BD_PA_lemma, rx_0receive_new_frame_PRESERVES_CPPI_RAM_lemma]);

val rx_0receive_new_frame_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_0receive_new_frame env`` THEN
  ASM_REWRITE_TAC [rx_0receive_new_frame_PRESERVES_RX_SOP_BD_PA_lemma, rx_0receive_new_frame_PRESERVES_CPPI_RAM_lemma]);

val rx_0receive_new_frame_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic'' : nic_state``] receive_frame_PRESERVES_RX_SUBINVARIANT_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPECL [``nic'' : nic_state``, ``nic' : nic_state``] rx_1fetch_next_bd_SUBINVARIANT_IMP_UNSEEN_BD_QUEUE_EQ_CURRENT_BD_PA_APPEND_UNSEEN_BD_QUEUE_NEW_STATE_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic''`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic'' : nic_state``, ``nic' : nic_state`` ] rx_1fetch_next_bd_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  REFLECT_ASM_TAC ``nic'.regs.CPPI_RAM = nic''.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``nic''.regs.CPPI_RAM = nic'.regs.CPPI_RAM`` ``RX_INVARIANT_BD_QUEUE_WELL_DEFINED q m`` THEN
  ASM_RW_ASM_TAC ``q = q' ++ q''`` ``RX_INVARIANT_BD_QUEUE_WELL_DEFINED q m`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``[nic''.rx.current_bd_pa]``, ``rx_unseen_bd_queue nic'``, ``nic'.regs.CPPI_RAM``] RX_INVARIANT_BD_QUEUE_WELL_DEFINED_IMP_SUFFIX_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    RX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_NOT_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_BD_QUEUE_STRUCTURE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
