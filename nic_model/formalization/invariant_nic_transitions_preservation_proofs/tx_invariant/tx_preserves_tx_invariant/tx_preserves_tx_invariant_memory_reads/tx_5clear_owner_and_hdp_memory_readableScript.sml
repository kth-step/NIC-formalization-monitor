open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_5clear_owner_and_hdp_lemmasTheory;
open txInvariantMemoryReadsTheory;
open txInvariantTheory;

val _ = new_theory "tx_5clear_owner_and_hdp_memory_readable";

val TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_READABLE_BD_QUEUE_lemma = prove (
  ``!nic nic' READABLE.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_def, listTheory.EVERY_DEF]);



(******************************************************************************)



val TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma = prove (
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def]);


(******************************************************************************)



val TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma = prove (
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def]);



(******************************************************************************)



val TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma = prove (
  ``!nic nic' READABLE.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    TX_INVARIANT_MEMORY_READABLE_STATE nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_STATE_def]);



(******************************************************************************)



(* Preservation of the complete invariant of the transmission automaton. *)
val TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic nic' READABLE.
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_5clear_owner_and_hdpTheory.TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma)) THEN
  ASSUME_TAC(CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

