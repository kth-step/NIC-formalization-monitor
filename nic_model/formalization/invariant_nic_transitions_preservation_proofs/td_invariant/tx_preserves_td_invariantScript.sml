open HolKernel Parse boolLib bossLib;
open helperTactics;
open tdInvariantTheory;
open tx_transition_definitionsTheory;
open tx_invariant_well_defined_lemmasTheory;
open qdInvariantTheory;
open bd_queueTheory;
open bd_listTheory;
open tx_state_lemmasTheory;
open tdTheory;
open txInvariantWellDefinedTheory;
open tx_state_definitionsTheory;
open txInvariantTheory;
open tx_transition_lemmasTheory;
open rx_bd_queueTheory;
open rx_state_lemmasTheory;

val _ = new_theory "tx_preserves_td_invariant";

val TX_STATE_NOT_BD_QUEUE_EMPTY_TX_SUBINVARIANTs_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_lemma = store_thm (
  "TX_STATE_NOT_BD_QUEUE_EMPTY_TX_SUBINVARIANTs_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_lemma",
  ``!nic.
    TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic
    ==>
    BD_IN_CPPI_RAM nic.tx.current_bd_pa``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``tx_bd_queue nic``] TX_INVARIANT_BD_PA_IN_QUEUE_AND_QUEUE_LOCATION_DEFINED_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic
    ==>
    TX_STATE_NOT_BD_QUEUE_EMPTY nic``,
  GEN_TAC THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  REWRITE_TAC [TX_STATE_NOT_BD_QUEUE_EMPTY_def] THEN
  REWRITE_TAC [GSYM TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_EQ_TX_STATE_CASESs_lemma] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_EQ_TX_STATE_CASESs_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_REWRITE_TAC []);

val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_lemma = store_thm (
  "TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_lemma",
  ``!nic.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic
    ==>
    BD_IN_CPPI_RAM nic.tx.current_bd_pa``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_NOT_BD_QUEUE_EMPTY_TX_SUBINVARIANTs_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_RX_STATE_TRANSITION_ENABLEs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_NOT_OVERLAP_RX_BD_QUEUE_lemma = store_thm (
  "TX_RX_STATE_TRANSITION_ENABLEs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_NOT_OVERLAP_RX_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    QD_INVARIANT nic /\
    MEM nic.tx.current_bd_pa (tx_bd_queue nic)
    ==>
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  RW_ASM_TAC ``BD_QUEUEs_DISJOINT q1 q2`` BD_QUEUEs_DISJOINT_def THEN
  MATCH_MP_TAC MEM_NO_BD_LIST_OVERLAP_IMP_BD_NOT_OVERLAP_BDs_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  ASM_REWRITE_TAC []);

val TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_NOT_OVERLAP_RX_BD_QUEUE_lemma = store_thm (
  "TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_NOT_OVERLAP_RX_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    QD_INVARIANT nic
    ==>
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_RX_STATE_TRANSITION_ENABLEs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_NOT_OVERLAP_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_IN_RX_BD_QUEUE_lemma = store_thm (
  "TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    QD_INVARIANT nic
    ==>
    BD_IN_CPPI_RAM nic.tx.current_bd_pa /\
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_NOT_OVERLAP_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_INVARIANT_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_IN_RX_BD_QUEUE_lemma = store_thm (
  "TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_INVARIANT_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_IN_RX_BD_QUEUE_lemma",
  ``!nic READABLE.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TX_INVARIANT nic READABLE /\
    QD_INVARIANT nic
    ==>
    BD_IN_CPPI_RAM nic.tx.current_bd_pa /\
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_SUBINVARIANTs_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_IN_CPPI_RAM_DEP_lemma = store_thm (
  "BD_IN_CPPI_RAM_DEP_lemma",
  ``!nic nic'.
    BD_IN_CPPI_RAM nic.tx.current_bd_pa /\
    (nic'.tx.current_bd_pa = nic .tx.current_bd_pa)
    ==>
    BD_IN_CPPI_RAM nic'.tx.current_bd_pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val BD_NOT_OVERLAP_BDs_DEP_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_DEP_lemma",
  ``!nic nic'.
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic) /\
    (nic'.tx.current_bd_pa = nic .tx.current_bd_pa) /\
    (nic'.rx = nic.rx) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    BD_NOT_OVERLAP_BDs nic'.tx.current_bd_pa (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_bd_queue_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_AUTONOMOUS_TRANSITION_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_PRESERVES_TD_INVARIANT_lemma",
  ``!nic env nic' mr' READABLE.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT nic READABLE /\
    QD_INVARIANT nic
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_INVARIANT_def] THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_AUTONOMOUS_TRANSITION_NEXT_TX_STATE_IDLE_IMP_PRESERVES_IT_TX_CURRENT_BD_PA_RX_RD_REGS_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma)) THEN
  ASM_RW_ASM_TAC ``nic'.it = nic.it`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  KEEP_ASM_RW_ASM_TAC ``nic'.tx.current_bd_pa = nic.tx.current_bd_pa`` ``nic'.tx.current_bd_pa ≠ 0w`` THEN
  RW_ASM_TAC ``nic.tx.current_bd_pa ≠ 0w`` (GSYM TD_WRITE_CURRENT_BD_PA_def) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_RX_STATE_TRANSITION_ENABLEs_TD_WRITE_CURRENT_BD_PA_TX_INVARIANT_QD_INVARIANT_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_IN_RX_BD_QUEUE_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_IN_CPPI_RAM_DEP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_NOT_OVERLAP_BDs_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TD_INVARIANT_lemma",
  ``!nic mr nic' READABLE.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_INVARIANT_def] THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_3process_memory_read_reply_NEXT_STATE_NOT_IDLE_lemma)) THEN
  ASM_RW_ASM_TAC ``TX_STATE_IDLE nic'`` ``~TX_STATE_IDLE nic'`` THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val _ = export_theory();

