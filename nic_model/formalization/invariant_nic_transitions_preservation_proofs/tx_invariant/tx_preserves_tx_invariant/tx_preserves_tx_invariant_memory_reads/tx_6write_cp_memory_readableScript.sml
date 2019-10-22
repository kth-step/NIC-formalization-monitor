open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_6write_cp_lemmasTheory;
open tx_invariant_memory_reads_lemmasTheory;
open txInvariantMemoryReadsTheory;
open txInvariantTheory;

val _ = new_theory "tx_6write_cp_memory_readable";

val TX_write_cp_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = prove (
  ``!nic env nic' READABLE.
    (nic' = tx_6write_cp env nic) /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_PRESERVED_SOP_BD_PA_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)



val TX_write_cp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma = prove (
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_NEXT_STATE_NEQ_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def]);



(******************************************************************************)



val TX_write_cp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma = prove (
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_NEXT_STATE_NEQ_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def]);



(******************************************************************************)



val TX_write_cp_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma = prove (
  ``!nic env nic' READABLE.
    (nic' = tx_6write_cp env nic)
    ==>
    TX_INVARIANT_MEMORY_READABLE_STATE nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_NEXT_STATE_NEQ_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_STATE_def]);




(******************************************************************************)




(* Preservation of the complete invariant of the transmission automaton. *)
val TX_write_cp_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_write_cp_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic env nic' READABLE.
    (nic' = tx_6write_cp env nic) /\
    TX_STATE_WRITE_CP nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_6write_cpTheory.TX_write_cp_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma)) THEN
  ASSUME_TAC(CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

