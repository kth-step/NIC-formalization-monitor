open HolKernel Parse boolLib bossLib;
open helperTactics;
open bd_queueTheory;
open bd_listTheory;
open txInvariantTheory;
open tx_transition_NOT_EXPANDS_TX_BD_QUEUETheory;
open rxInvariantTheory;
open rxInvariantWellDefinedTheory;
open tx_transition_preserves_other_automataTheory;
open rxInvariantWellDefinedLemmasTheory;
open tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUETheory;
open tx_transition_definitionsTheory;
open qdInvariantTheory;
open tx_transition_lemmasTheory;

val _ = new_theory "tx_preserves_qd_invariant";

val tx_transition_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma = store_thm (
  "tx_transition_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma",
  ``!nic env nic' mr' READABLE q.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) q
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUEs_DISJOINT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``NO_BD_LIST_OVERLAP q1 q2`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [NO_BD_LIST_OVERLAP_SYM_lemma] thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_NOT_EXPANDS_TX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``tx_bd_queue nic``, ``tx_bd_queue nic'``] NO_BD_LIST_OVERLAP_IN_LIST1_IMP_IN_LIST2_IMP_NO_BD_LIST_OVERLAP_lemma)) THEN
  ASM_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma]);

val tx_memory_read_reply_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma",
  ``!nic mr nic' READABLE q.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) q
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUEs_DISJOINT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``NO_BD_LIST_OVERLAP q1 q2`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [NO_BD_LIST_OVERLAP_SYM_lemma] thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_NOT_EXPANDS_TX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``tx_bd_queue nic``, ``tx_bd_queue nic'``] NO_BD_LIST_OVERLAP_IN_LIST1_IMP_IN_LIST2_IMP_NO_BD_LIST_OVERLAP_lemma)) THEN
  ASM_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma]);

val tx_transition_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "tx_transition_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUEs_DISJOINT_def] THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_transition_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  PAT_ASSUM ``NO_BD_LIST_OVERLAP q1 q2`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [NO_BD_LIST_OVERLAP_SYM_lemma] thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic' : nic_state``, ``mr' : memory_request option``, ``rx_bd_queue nic``] tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_memory_read_reply_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic mr nic' READABLE WRITABLE.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUEs_DISJOINT_def] THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_memory_read_reply_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  PAT_ASSUM ``NO_BD_LIST_OVERLAP q1 q2`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [NO_BD_LIST_OVERLAP_SYM_lemma] thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``mr : memory_request``, ``nic' : nic_state``, ``rx_bd_queue nic``] tx_memory_read_reply_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_transition_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma = store_thm (
  "tx_transition_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic' : nic_state``, ``mr' : memory_request option``, ``READABLE : bd_pa_type -> bool``, ``rx_bd_queue nic``] tx_transition_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_PRESERVES_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_AUTONOMOUS_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic')``,
  REWRITE_TAC [TX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [GSYM boolTheory.CONJ_ASSOC, tx_transition_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma]);

val tx_memory_read_reply_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma",
  ``!nic mr nic' READABLE WRITABLE.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``mr : memory_request``, ``nic' : nic_state``, ``READABLE : bd_pa_type -> bool``, ``rx_bd_queue nic``] tx_memory_read_reply_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_RX_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``rx_bd_queue nic' = rx_bd_queue nic`` THEN
  ASM_RW_ASM_TAC ``rx_bd_queue nic = rx_bd_queue nic'`` ``BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic)`` THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma",
  ``!nic mr nic' READABLE WRITABLE.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic')``,
  REWRITE_TAC [TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def] THEN
  REWRITE_TAC [GSYM boolTheory.CONJ_ASSOC, tx_memory_read_reply_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma]);

val TX_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT nic READABLE /\
    RX_INVARIANT nic WRITABLE /\
    QD_INVARIANT nic
    ==>
    QD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  REPEAT (PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_AUTONOMOUS_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_QD_INVARIANT_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_QD_INVARIANT_lemma",
  ``!nic mr nic' READABLE WRITABLE.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' /\
    TX_INVARIANT nic READABLE /\
    RX_INVARIANT nic WRITABLE /\
    QD_INVARIANT nic
    ==>
    QD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [QD_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_REVERSED_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  REPEAT (PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma)) THEN
  ASM_REWRITE_TAC []);  

val _ = export_theory();

