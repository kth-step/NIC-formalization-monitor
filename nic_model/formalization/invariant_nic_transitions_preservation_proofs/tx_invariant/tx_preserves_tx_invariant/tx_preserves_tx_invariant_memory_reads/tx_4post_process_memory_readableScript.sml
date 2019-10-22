open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_4post_process_lemmasTheory;
open txInvariantMemoryReadsTheory;
open txInvariantTheory;

val _ = new_theory "tx_4post_process_memory_readable";

val TX_post_process_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = prove (
  ``!nic nic' READABLE.
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `LAST_BD nic.tx.current_bd` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);



(******************************************************************************)



val TX_post_process_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma = prove (
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_NEXT_STATE_NEQ_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def]);



(******************************************************************************)



val TX_post_process_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma = prove (
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_NEXT_STATE_NEQ_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def]);



(******************************************************************************)



val TX_post_process_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma = prove (
  ``!nic nic' READABLE.
    (nic' = tx_4post_process nic)
    ==>
    TX_INVARIANT_MEMORY_READABLE_STATE nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_NEXT_STATE_NEQ_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_STATE_def]);



(******************************************************************************)



(* Preservation of the complete invariant of the transmission automaton. *)
val TX_post_process_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_post_process_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic nic' READABLE.
    (nic' = tx_4post_process nic) /\
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_processTheory.TX_post_process_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma)) THEN
  ASSUME_TAC(CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
