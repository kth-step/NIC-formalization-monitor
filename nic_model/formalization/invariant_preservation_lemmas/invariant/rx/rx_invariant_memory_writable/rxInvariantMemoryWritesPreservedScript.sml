open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantMemoryWritesTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedTheory;
open bd_listTheory;
open bdTheory;
open rx_state_lemmasTheory;
open rxInvariantTheory;
open rxInvariantWellDefinedPreservedTheory;

val _ = new_theory "rxInvariantMemoryWritesPreserved";

val RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_PRESERVED_lemma",
  ``!nic nic' WRITABLE.
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_SUBINVARIANT_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_RW_ASM_TAC ``rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic`` ``MEM e q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_RW_ASM_TAC ``rx_bd_queue nic = q`` ``EQ_BDs q m m'`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``rx_seen_bd_queue : bd_pa_type list``, ``rx_unseen_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] EQ_BDs_IMP_EQ_SUFFIX_BDs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``rx_unseen_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``e : bd_pa_type``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_EQ_IMP_rx_read_bd_EQ_lemma)) THEN
  UNDISCH_TAC ``BD_ADDRESSES_WRITABLE_MEMORY e nic.regs.CPPI_RAM WRITABLE`` THEN
  REWRITE_TAC [BD_ADDRESSES_WRITABLE_MEMORY_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_CURRENT_BUFFER_WRITABLE_PRESERVED_lemma = store_thm (
  "RX_INVARIANT_CURRENT_BUFFER_WRITABLE_PRESERVED_lemma",
  ``!nic nic' WRITABLE.
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic WRITABLE /\
    (nic'.rx = nic.rx)
    ==>
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_PRESERVED_lemma = store_thm (
  "RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_PRESERVED_lemma",
  ``!nic nic'.
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic /\
    (nic'.rx = nic.rx)
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  RW_ASM_TAC ``RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic`` RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_def THEN
  REWRITE_TAC [RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_def] THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_PRESERVED_lemma = store_thm (
  "RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_PRESERVED_lemma",
  ``!nic nic'.
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic /\
    (nic'.rx = nic.rx)
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def] THEN
  REWRITE_TAC [RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_MEMORY_WRITABLE_PRESERVED_lemma = store_thm (
  "RX_INVARIANT_MEMORY_WRITABLE_PRESERVED_lemma",
  ``!nic nic' WRITABLE.
    RX_INVARIANT_MEMORY_WRITABLE nic WRITABLE /\
    RX_INVARIANT_WELL_DEFINED nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    RX_INVARIANT_MEMORY_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_def] THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_CURRENT_BUFFER_WRITABLE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_MEMORY_PRESERVED_lemma = store_thm (
  "RX_INVARIANT_MEMORY_PRESERVED_lemma",
  ``!nic nic' WRITABLE.
    RX_INVARIANT_MEMORY nic WRITABLE /\
    (nic'.dead = nic.dead) /\
    (nic'.it.state = nic.it.state) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd.state = nic.rd.state) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET)
    ==>
    RX_INVARIANT_MEMORY nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_WELL_DEFINED_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_MEMORY_WRITABLE_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
