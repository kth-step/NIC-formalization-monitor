open HolKernel Parse boolLib bossLib;
open helperTactics;
open rdInvariantTheory;
open rd_state_definitionsTheory;
open rx_transition_definitionsTheory;
open rx_state_definitionsTheory;
open schedulerTheory;

val _ = new_theory "rd_invariant_lemmas";

val EQ_RD_STATE_EQ_RX_SOP_BD_PA_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "EQ_RD_STATE_EQ_RX_SOP_BD_PA_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic nic'.
    (nic'.rd.state = nic.rd.state) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val EQ_RX_STATE_EQ_RX_SOP_BD_PA_EQ_RD_STATE_EQ_IT_STATE_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma = store_thm (
  "EQ_RX_STATE_EQ_RX_SOP_BD_PA_EQ_RD_STATE_EQ_IT_STATE_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma",
  ``!nic nic'.
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rd.state = nic.rd.state) /\
    (nic'.it.state = nic.it.state) /\
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic
    ==>
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RX_ADVANCES_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RX_ENABLE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

