open HolKernel Parse boolLib bossLib;
open helperTactics;
open txInvariantTheory;
open tx_transition_preserves_tx_invariant_well_definedTheory;
open txInvariantWellDefinedTheory;
open rxInvariantTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedLemmasTheory;
open tx_transition_preserves_other_automataTheory;
open bd_listTheory;
open tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUETheory;
open it_state_lemmasTheory;
open rxInvariantMemoryWritesPreservedTheory;
open tx_transition_definitionsTheory;
open bd_queueTheory;
open tx_transition_lemmasTheory;
open qdInvariantTheory;

val _ = new_theory "tx_preserves_rx_invariant";

val tx_transition_PRESERVES_DEAD_lemma = store_thm (
  "tx_transition_PRESERVES_DEAD_lemma",
  ``!nic env  nic' mr' READABLE.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic'`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_NOT_DEAD nic`` TX_INVARIANT_NOT_DEAD_def THEN
  RW_ASM_TAC ``TX_INVARIANT_NOT_DEAD nic'`` TX_INVARIANT_NOT_DEAD_def THEN
  ASM_REWRITE_TAC []);

val tx_memory_read_reply_PRESERVES_DEAD_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_DEAD_lemma",
  ``!nic mr nic' READABLE.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic'`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_NOT_DEAD nic`` TX_INVARIANT_NOT_DEAD_def THEN
  RW_ASM_TAC ``TX_INVARIANT_NOT_DEAD nic'`` TX_INVARIANT_NOT_DEAD_def THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_MEMORY_IMP_RX_BD_QUEUE_IN_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_MEMORY_IMP_RX_BD_QUEUE_IN_CPPI_RAM_lemma",
  ``!nic WRITABLE.
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    BDs_IN_CPPI_RAM (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_MEMORY_IMP_TX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "TX_INVARIANT_MEMORY_IMP_TX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic READABLE.
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_WELL_DEFINED nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def, boolTheory.AND1_THM]);

val tx_transition_PRESERVES_RX_INVARIANT_MEMORY_lemma = store_thm (
  "tx_transition_PRESERVES_RX_INVARIANT_MEMORY_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    NO_BD_LIST_OVERLAP (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    RX_INVARIANT_MEMORY nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_PRESERVES_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_INVARIANT_MEMORY_IMP_RX_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_INVARIANT_MEMORY_IMP_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (ONCE_REWRITE_RULE [NO_BD_LIST_OVERLAP_SYM_lemma] (SPECL [``nic : nic_state``, ``env : environment``, ``nic' : nic_state``, ``mr' : memory_request option``, ``rx_bd_queue nic``] tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma))) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rd_state_lemmasTheory.RD_EQ_IMP_RD_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_MEMORY_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma",
  ``!nic mr env nic' mr' READABLE WRITABLE.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT nic READABLE /\
    RX_INVARIANT nic WRITABLE /\
    QD_INVARIANT nic
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  RW_KEEP_ASM_TAC ``TX_AUTONOMOUS_TRANSITION nic env nic' mr'`` TX_AUTONOMOUS_TRANSITION_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT nic READABLE`` TX_INVARIANT_def THEN
  PAT_ASSUM ``P ==> TX_INVARIANT_MEMORY nic READABLE`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  REPEAT (PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm))) THEN  
  RW_ASM_TAC ``BD_QUEUEs_DISJOINT q1 q2`` BD_QUEUEs_DISJOINT_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_PRESERVES_RX_INVARIANT_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_memory_read_reply_PRESERVES_RX_INVARIANT_MEMORY_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_RX_INVARIANT_MEMORY_lemma",
  ``!nic mr nic' READABLE WRITABLE.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    NO_BD_LIST_OVERLAP (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    RX_INVARIANT_MEMORY nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_INVARIANT_MEMORY_IMP_RX_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_INVARIANT_MEMORY_IMP_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (ONCE_REWRITE_RULE [NO_BD_LIST_OVERLAP_SYM_lemma] (SPECL [``nic : nic_state``, ``mr : memory_request``, ``nic' : nic_state``, ``rx_bd_queue nic``] tx_memory_read_reply_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma))) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rd_state_lemmasTheory.RD_EQ_IMP_RD_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_MEMORY_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_RX_INVARIANT_lemma",
  ``!nic mr nic' READABLE WRITABLE.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' /\
    TX_INVARIANT nic READABLE /\
    RX_INVARIANT nic WRITABLE /\
    QD_INVARIANT nic
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  RW_KEEP_ASM_TAC ``TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'`` TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT nic READABLE`` TX_INVARIANT_def THEN
  PAT_ASSUM ``P ==> TX_INVARIANT_MEMORY nic READABLE`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_REVERSED_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  REPEAT (PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm))) THEN  
  RW_ASM_TAC ``BD_QUEUEs_DISJOINT q1 q2`` BD_QUEUEs_DISJOINT_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_RX_INVARIANT_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

