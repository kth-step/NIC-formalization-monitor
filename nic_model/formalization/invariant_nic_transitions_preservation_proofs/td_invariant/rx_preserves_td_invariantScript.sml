open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_transition_definitionsTheory;
open td_invariant_preservation_definitionsTheory;
open tdInvariantTheory;
open tx_state_definitionsTheory;
open tdTheory;
open td_transition_invariant_lemmasTheory;
open bd_listTheory;
open rxInvariantTheory;
open rx_transition_lemmasTheory;
open it_transition_definitionsTheory;
open rx_transition_preserves_other_automataTheory;
open rx_transition_NOT_EXPANDS_RX_BD_QUEUETheory;

val _ = new_theory "rx_preserves_td_invariant";

val NIC_DELTA_PRESERVES_TX_IMP_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "NIC_DELTA_PRESERVES_TX_IMP_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma",
  ``!nic_delta.
    NIC_DELTA_PRESERVES_TX nic_delta
    ==>
    NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM nic_delta``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_def] THEN
  REWRITE_TAC [NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [TX_STATE_IDLE_def] THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_NOT_EXPANDING_RX_BD_QUEUE_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "NIC_DELTA_NOT_EXPANDING_RX_BD_QUEUE_PRESERVES_TD_INVARIANT_lemma",
  ``!nic nic_delta nic'.
    (nic' = nic_delta nic) /\
    TD_INVARIANT nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    IN_LIST1_IMP_IN_LIST2 (rx_bd_queue nic') (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_IT nic_delta /\
    NIC_DELTA_PRESERVES_TX nic_delta
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_INVARIANT_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL NIC_DELTA_PRESERVES_TX_IMP_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_MP_TD_STATE_WRITE_CPPI_RAM_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``rx_bd_queue nic'``, ``rx_bd_queue nic``] BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_SUBLIST_lemma)) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_TX nic_delta`` NIC_DELTA_PRESERVES_TX_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  REFLECT_ASM_TAC ``nic' : nic_state = nic_delta nic`` THEN
  ASM_RW_ASM_TAC ``nic_delta nic = nic'`` ``(nic_delta : nic_delta_type nic).tx = nic.tx`` THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_RX_INVARIANT_IMP_RX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_RX_INVARIANT_IMP_RX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic env nic' mr' WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT_WELL_DEFINED nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val rx_transition_PRESERVES_IT_lemma = store_thm (
  "rx_transition_PRESERVES_IT_lemma",
  ``!env. NIC_DELTA_PRESERVES_IT (FST o rx_transition env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_IT_def] THEN
  GEN_TAC THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [rx_transition_FST_SND_EQ_lemma] (SPECL [``nic : nic_state``, ``env : environment``, ``FST (rx_transition env nic)``, ``SND (rx_transition env nic)``] rx_transition_PRESERVES_OTHER_AUTOMATA_lemma)]);

val rx_transition_PRESERVES_TX_lemma = store_thm (
  "rx_transition_PRESERVES_TX_lemma",
  ``!env. NIC_DELTA_PRESERVES_TX (FST o rx_transition env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_def] THEN
  GEN_TAC THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [rx_transition_FST_SND_EQ_lemma] (SPECL [``nic : nic_state``, ``env : environment``, ``FST (rx_transition env nic)``, ``SND (rx_transition env nic)``] rx_transition_PRESERVES_OTHER_AUTOMATA_lemma)]);

val RX_AUTONOMOUS_TRANSITION_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_TD_INVARIANT_lemma",
  ``!nic env nic' mr' WRITABLE.
  RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
  RX_INVARIANT nic WRITABLE /\
  TD_INVARIANT nic
  ==>
  TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_NOT_EXPANDING_RX_BD_QUEUE_PRESERVES_TD_INVARIANT_lemma THEN
  Q.EXISTS_TAC `nic` THEN
  Q.EXISTS_TAC `FST o rx_transition env` THEN
  REWRITE_TAC [rx_transition_PRESERVES_IT_lemma] THEN
  REWRITE_TAC [rx_transition_PRESERVES_TX_lemma] THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_TRANSITION_lemma)) THEN
  PAT_ASSUM ``x = y`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM rx_transition_FST_SND_EQ_lemma] thm)) THEN
  RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC rx_transition_NOT_EXPANDS_RX_BD_QUEUE_lemma THEN
  Q.EXISTS_TAC `env` THEN
  Q.EXISTS_TAC `mr'` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_RX_INVARIANT_IMP_RX_INVARIANT_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

