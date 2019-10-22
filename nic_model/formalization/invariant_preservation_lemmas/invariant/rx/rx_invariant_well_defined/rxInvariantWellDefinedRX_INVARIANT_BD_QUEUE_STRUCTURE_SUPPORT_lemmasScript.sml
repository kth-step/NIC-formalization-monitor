open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_state_definitionsTheory;
open rx_bd_queueTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemmas";

val RX_STATE_IDLE_INIT_INITIALIZED_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_START_FROM_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_START_FROM_CURRENT_BD_PA_lemma",
  ``!nic.
    RX_STATE_IDLE nic /\
    IT_STATE_INITIALIZED nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_IDLE nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``IT_STATE_INITIALIZED nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``RX_STATE_IDLE nic`` RX_STATE_IDLE_def THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def, stateTheory.rx_abstract_state_case_def]);

val _ = export_theory();

