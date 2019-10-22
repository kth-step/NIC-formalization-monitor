open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_invariant_well_defined_lemmasTheory
open tx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open txInvariantWellDefinedTheory;
open bd_listTheory;
open tx_state_lemmasTheory;
open tx_state_definitionsTheory;

val _ = new_theory "txInvariantWellDefinedPreserved";

val TX_INVARIANT_BD_QUEUE_FINITE_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_FINITE_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  MATCH_MP_TAC BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_BD_QUEUE_NO_OVERLAP_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_NO_OVERLAP_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic.regs.CPPI_RAM /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def] THEN
  REWRITE_TAC [TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REWRITE_TAC [TX_LINUX_BD_SOP_EOP_def] THEN
  REWRITE_TAC [TX_LINUX_BD_SOP_def] THEN
  REWRITE_TAC [TX_LINUX_BD_EOP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic' = tx_bd_queue nic`` ``MEM e (tx_bd_queue nic')`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (SYM (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_EQ_IMP_TX_BD_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_def] THEN
  REWRITE_TAC [NOT_TX_BD_QUEUE_EMPTY_def] THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] TX_STATE_NOT_BD_QUEUE_EMPTY_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    (nic'.tx = nic.tx)
    ==>
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] TX_STATE_NOT_BD_QUEUE_EMPTY_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (SYM (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_EQ_IMP_TX_BD_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic) nic.regs.CPPI_RAM /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_FINITE_EQ_TX_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic' = tx_bd_queue nic`` ``MEM e q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (SYM (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_EQ_IMP_TX_BD_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic) nic.regs.CPPI_RAM /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_FINITE_EQ_TX_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic' = tx_bd_queue nic`` ``MEM e q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (SYM (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_EQ_IMP_TX_BD_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val EQ_BDs_IN_NON_EMPTY_TX_BD_QUEUE_IMP_EQ_TAIL_BDs_lemma = store_thm (
  "EQ_BDs_IN_NON_EMPTY_TX_BD_QUEUE_IMP_EQ_TAIL_BDs_lemma",
  ``!nic nic'.
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM /\
    tx_bd_queue nic <> []
    ==>
    EQ_BDs (TL (tx_bd_queue nic)) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  Cases_on `tx_bd_queue nic` THEN
  REWRITE_TAC [listTheory.TL, EQ_BDs_HD_TL_EQ_BD_EQ_HD_EQ_BDs_TL_lemma] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma",
  ``!q CPPI_RAM CPPI_RAM'.
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM /\
    EQ_BDs q CPPI_RAM CPPI_RAM'
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``q : bd_pa_type list``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (SYM (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_EQ_IMP_TX_BD_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_EQ_IMP_TX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  MATCH_MP_TAC TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_FINITE_EQ_TX_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_EQ_IMP_TX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_FINITE_EQ_TX_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  PAT_ASSUM ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q m`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic`` TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH (REWRITE_RULE [NOT_TX_BD_QUEUE_EMPTY_def] thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_BDs_IN_NON_EMPTY_TX_BD_QUEUE_IMP_EQ_TAIL_BDs_lemma)) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  CONJ_TAC THENL
  [
   MATCH_MP_TAC TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_PRESERVED_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   ASM_REWRITE_TAC []
  ]);

val TX_INVARIANT_CURRENT_BD_EOP_STATE_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_CURRENT_BD_EOP_STATE_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic /\
    (nic'.tx = nic.tx)
    ==>
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_EOP_STATE_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] TX_STATE_NOT_BD_QUEUE_EMPTY_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_PRESERVED_lemma = store_thm (
  "BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_PRESERVED_lemma",
  ``!nic nic'.
    BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic /\
    (nic'.tx = nic.tx)
    ==>
    BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_EQ_IMP_TX_STATE_EQ_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val tx_state_application = (#1 o dest_disj o concl) thm in
    let val tx_id = txLib.tx_transition_state_application_to_tx_id tx_state_application in
    let val lemma = txLib.get_tx_conjunct TX_STATE_DEP_CONJ_lemmas tx_id in
      ASSUME_TAC thm THEN
      ASM_CASES_TAC tx_state_application THENL
      [
       ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL lemma)) THEN
       ASM_REWRITE_TAC []
       ,
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end end)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_POST_PROCESS_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_PRESERVED_lemma = store_thm (
  "CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_PRESERVED_lemma",
  ``!nic nic'.
    TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    CURRENT_BD_NDP_EQ_CPPI_RAM_NDP nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    CURRENT_BD_NDP_EQ_CPPI_RAM_NDP nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] MEM_EQ_BDs_Q_IMP_BD_EQ_lemma)) THEN
  ASSUME_TAC (SYM (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_EQ_IMP_TX_BD_EQ_lemma))) THEN
  REWRITE_TAC [GSYM tx_read_ndp_EQ_read_ndp_lemma] THEN
  RW_ASM_TAC ``nic.tx.current_bd.ndp = read_ndp a m`` (GSYM tx_read_ndp_EQ_read_ndp_lemma) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic nic'.
    BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic /\
    (nic'.tx.state = nic.tx.state)
    ==>
    TX_STATE_NOT_BD_QUEUE_EMPTY nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def] THEN
  REWRITE_TAC [TX_STATE_NOT_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  REWRITE_TAC [boolTheory.DISJ_ASSOC] THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  ASM_REWRITE_TAC [GSYM boolTheory.DISJ_ASSOC]);

val TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_PRESERVED_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_EQ_IMP_TX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_STATE nic /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_CURRENT_BD_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_STATE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_CURRENT_BD_EOP_STATE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_WELL_DEFINED_PRESERVED_lemma",
  ``!nic nic'.
    TX_INVARIANT_WELL_DEFINED nic /\
    (nic'.dead = nic.dead) /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    TX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  REWRITE_TAC [TX_INVARIANT_NOT_DEAD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_FINITE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_NO_OVERLAP_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
