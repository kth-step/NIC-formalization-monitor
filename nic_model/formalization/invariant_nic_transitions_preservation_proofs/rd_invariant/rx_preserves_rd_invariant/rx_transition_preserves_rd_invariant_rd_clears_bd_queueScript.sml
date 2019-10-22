open HolKernel Parse boolLib bossLib;
open helperTactics;
open rdInvariantTheory;
open rx_transition_lemmasTheory;
open rd_state_definitionsTheory;
open rx_transition_definitionsTheory;
open rx_state_lemmasTheory;
open rx_state_definitionsTheory;
open rx_transition_preserves_other_automataTheory;

val _ = new_theory "rx_transition_preserves_rd_invariant_rd_clears_bd_queue";

val RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic
    ==>
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_transition_definitionsTheory.RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_INVARIANT_RX_ADVANCES_BD_QUEUE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  ASM_REWRITE_TAC []);

val RD_INVARIANT_RD_CLEARS_BD_QUEUE_DEP_lemma = store_thm (
  "RD_INVARIANT_RD_CLEARS_BD_QUEUE_DEP_lemma",
  ``!nic nic'.
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rd = nic.rd) /\
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``(nic' : nic_state).rd = nic.rd`` ``nic'.rd.state = rd_write_cp`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic /\
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic'`` RD_INVARIANT_RX_ADVANCES_BD_QUEUE_def THEN
  ASM_CASES_TAC ``RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'`` THENL
  [
   PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
   ASM_REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def]
   ,
   ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` NOT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_IDLE_lemma)) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_NEXT_STATE_EQ_rx_19write_cp_CURRENT_STATE_WRITE_CP_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma)) THEN
   SPLIT_ASM_TAC THEN
   ASM_CASES_TAC ``nic' = rx_19write_cp env nic`` THENL
   [
    ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_lemmasTheory.rx_19write_cp_NOT_MODIFIED_lemma)) THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_INVARIANT_RD_CLEARS_BD_QUEUE_DEP_lemma)) THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_INVARIANT_RD_CLEARS_BD_QUEUE_DEP_lemma)) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val _ = export_theory();
