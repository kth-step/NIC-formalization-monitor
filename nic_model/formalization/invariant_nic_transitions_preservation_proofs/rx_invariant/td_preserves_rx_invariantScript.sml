open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantTheory;
open rxInvariantMemoryWritesPreservedTheory;
open it_state_lemmasTheory;
open rx_state_lemmasTheory;
open bd_listTheory;
open td_transition_invariant_lemmasTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedLemmasTheory;
open tdInvariantTheory;

val _ = new_theory "td_preserves_rx_invariant";

val TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_PRESERVES_RX_INVARIANT_lemma",
  ``!nic env nic' WRITABLE.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    ~TD_WRITE_CURRENT_BD_PA nic /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_INVARIANT_MEMORY_PRESERVED_lemma THEN
  Q.EXISTS_TAC `nic` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_PRESERVATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma))) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC [EQ_BDs_SYM_lemma]);

val td_transition_preserves_RX_BD_QUEUE_lemma = store_thm (
  "td_transition_preserves_RX_BD_QUEUE_lemma",
  ``!nic env.
    BD_IN_CPPI_RAM nic.tx.current_bd_pa /\
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic) /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM (td_transition env nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BD_PRESERVES_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  Q.EXISTS_TAC `nic.tx.current_bd_pa` THEN
  EXISTS_TAC ``td_transition_cppi_ram_write_step_bd_pas env nic`` THEN
  RW_ASM_TAC ``RX_INVARIANT_WELL_DEFINED nic`` RX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [td_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma]);

val TD_INVARIANT_WRITE_CURRENT_BD_PA_TX_STATE_IDLE_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_OVERLAPPING_RX_BD_QUEUE_lemma = store_thm (
  "TD_INVARIANT_WRITE_CURRENT_BD_PA_TX_STATE_IDLE_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_OVERLAPPING_RX_BD_QUEUE_lemma",
  ``!nic.
    TD_INVARIANT nic /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TX_STATE_IDLE nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
    ==>
    BD_IN_CPPI_RAM nic.tx.current_bd_pa /\
    BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [TD_INVARIANT_def] THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_TD_WRITE_CURRENT_BD_PA_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_TD_WRITE_CURRENT_BD_PA_PRESERVES_RX_INVARIANT_lemma",
  ``!nic env nic' WRITABLE.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    TD_WRITE_CURRENT_BD_PA nic /\
    TD_INVARIANT nic /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_INVARIANT_MEMORY_PRESERVED_lemma THEN
  Q.EXISTS_TAC `nic` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_RX_BUFFER_OFFSET_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma))) THEN
  RW_ASM_TAC ``RX_INVARIANT nic WRITABLE`` RX_INVARIANT_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC td_transition_preserves_RX_BD_QUEUE_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_INVARIANT_WRITE_CURRENT_BD_PA_TX_STATE_IDLE_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TX_CURRENT_BD_PA_IN_CPPI_RAM_NOT_OVERLAPPING_RX_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_MEMORY nic WRITABLE`` RX_INVARIANT_MEMORY_def THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma",
  ``!nic env nic' WRITABLE.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    TD_INVARIANT nic /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_CASES_TAC ``TD_WRITE_CURRENT_BD_PA nic`` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_TD_WRITE_CURRENT_BD_PA_PRESERVES_RX_INVARIANT_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_PRESERVES_RX_INVARIANT_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val _ = export_theory();

