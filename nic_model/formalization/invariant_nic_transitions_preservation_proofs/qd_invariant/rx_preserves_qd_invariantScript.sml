open HolKernel Parse boolLib bossLib;
open helperTactics;
open bd_queueTheory;
open rxInvariantTheory;
open rx_transition_NOT_EXPANDS_RX_BD_QUEUETheory;
open bd_listTheory;
open txInvariantTheory;
open txInvariantWellDefinedTheory;
open rx_transition_preserves_other_automataTheory;
open tx_invariant_well_defined_lemmasTheory;
open rx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUETheory;
open rx_transition_definitionsTheory;
open qdInvariantTheory;
open rx_transition_lemmasTheory;

val _ = new_theory "rx_preserves_qd_invariant";

val rx_transition_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma = store_thm (
  "rx_transition_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma",
  ``!nic env nic' mr' WRITABLE q.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT q (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT q (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUEs_DISJOINT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_MEMORY nic WRITABLE`` RX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_NOT_EXPANDS_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``rx_bd_queue nic``, ``rx_bd_queue nic'``] NO_BD_LIST_OVERLAP_IN_LIST1_IMP_IN_LIST2_IMP_NO_BD_LIST_OVERLAP_lemma)) THEN
  ASM_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma]);

val rx_transition_PRESERVES_TX_BD_QUEUE_lemma = store_thm (
  "rx_transition_PRESERVES_TX_BD_QUEUE_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUEs_DISJOINT_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic' : nic_state``, ``mr' : memory_request option``, ``tx_bd_queue nic``] rx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_BD_QUEUE_FINITE_EQ_TX_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_transition_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma = store_thm (
  "rx_transition_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic' : nic_state``, ``mr' : memory_request option``, ``WRITABLE : bd_pa_type -> bool``, ``tx_bd_queue nic``] rx_transition_PRESERVES_TX_BD_QUEUE_DISJOINT_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_PRESERVES_TX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT_MEMORY nic READABLE /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    BD_QUEUEs_DISJOINT (tx_bd_queue nic) (rx_bd_queue nic)
    ==>
    BD_QUEUEs_DISJOINT (tx_bd_queue nic') (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [GSYM boolTheory.CONJ_ASSOC, rx_transition_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma]);

val RX_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_QD_INVARIANT_lemma",
  ``!nic env nic' mr' READABLE WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
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
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  REPEAT (PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_PRESERVES_TX_RX_BD_QUEUEs_DISJOINT_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

