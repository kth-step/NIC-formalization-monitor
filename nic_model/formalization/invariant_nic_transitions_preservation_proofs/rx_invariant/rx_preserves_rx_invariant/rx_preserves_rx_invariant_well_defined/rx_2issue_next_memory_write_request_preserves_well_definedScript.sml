open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_2issue_next_memory_write_request_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_FINITE_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemmasTheory;

val _ = new_theory "rx_2issue_next_memory_write_request_preserves_well_defined";

val rx_2issue_next_memory_write_request_PRESERVES_NOT_DEAD_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_NOT_DEAD_lemma",
  ``!nic mr' nic'.
    ((nic',mr') = rx_2issue_next_memory_write_request nic) /\
    RX_INVARIANT_NOT_DEAD nic
    ==>
    RX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NOT_DEAD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_STRUCTURE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STORE_MORE_BYTES nic.rx` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_NOT_RX_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
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
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def]);

val rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``FST o rx_2issue_next_memory_write_request`` THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma] THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (SPEC ``rx_2issue_next_memory_write_request nic`` (INST_TYPE [alpha |-> ``: nic_state``, beta |-> ``: memory_request option``] pairTheory.PAIR))] thm)) THEN
  RW_ASM_TAC ``P`` pairTheory.PAIR_EQ THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``FST o rx_2issue_next_memory_write_request`` THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma] THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (SPEC ``rx_2issue_next_memory_write_request nic`` (INST_TYPE [alpha |-> ``: nic_state``, beta |-> ``: memory_request option``] pairTheory.PAIR))] thm)) THEN
  RW_ASM_TAC ``P`` pairTheory.PAIR_EQ THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STORE_MORE_BYTES nic.rx` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_STORE_MORE_BYTES_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_2issue_next_memory_write_request_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    RX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_NOT_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_STRUCTURE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_BD_QUEUE_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_RX_BUFFER_OFFSET_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

