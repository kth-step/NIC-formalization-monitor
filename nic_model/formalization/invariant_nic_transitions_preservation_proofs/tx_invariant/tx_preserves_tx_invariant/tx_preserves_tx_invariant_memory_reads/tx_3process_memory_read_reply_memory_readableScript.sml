open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_3process_memory_read_reply_lemmasTheory;
open tx_bd_queueTheory;
open txInvariantMemoryReadsTheory;
open txInvariantTheory;

val _ = new_theory "tx_3process_memory_read_reply_memory_readable";

val TX_process_memory_read_reply_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = prove (
  ``!nic mr nic' READABLE.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [tx_bd_queue_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM`` tx_bd_queue_def THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma = prove (
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NEXT_STATE_EQ_issue_next_memory_read_request_IMP_BYTES_LEFT_TO_REQUEST_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``TX_STATE_PROCESS_MEMORY_READ_REPLY nic`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_process_memory_read_reply_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma = prove (
  ``!nic mr nic' READABLE.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_MEMORY_READABLE_STATE nic READABLE
    ==>
    TX_INVARIANT_MEMORY_READABLE_STATE nic' READABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_STATE_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NEXT_STATE_EQ_issue_next_memory_read_request_IMP_BYTES_LEFT_TO_REQUEST_lemma)) THEN
   ASM_RW_ASM_TAC ``TX_STATE_PROCESS_MEMORY_READ_REPLY nic`` ``P ==> Q`` THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
   SPLIT_ASM_TAC THEN
   KEEP_ASM_RW_ASM_TAC ``nic'.tx.number_of_buffer_bytes_left_to_request = nic.tx.number_of_buffer_bytes_left_to_request`` ``nic'.tx.number_of_buffer_bytes_left_to_request >+ 0w`` THEN
   ASM_RW_ASM_TAC ``nic.tx.number_of_buffer_bytes_left_to_request >+ 0w`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
   SPLIT_ASM_TAC THEN
   KEEP_ASM_RW_ASM_TAC ``nic'.tx.number_of_buffer_bytes_left_to_request = nic.tx.number_of_buffer_bytes_left_to_request`` ``nic'.tx.number_of_buffer_bytes_left_to_request >+ 0w`` THEN
   ASM_RW_ASM_TAC ``TX_STATE_PROCESS_MEMORY_READ_REPLY nic`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``nic.tx.number_of_buffer_bytes_left_to_request >+ 0w`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
  ]);



(******************************************************************************)



(* Preservation of the complete invariant of the transmission automaton. *)
val TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic mr nic' READABLE.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_3process_memory_read_replyTheory.TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma)) THEN
  ASSUME_TAC(CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

