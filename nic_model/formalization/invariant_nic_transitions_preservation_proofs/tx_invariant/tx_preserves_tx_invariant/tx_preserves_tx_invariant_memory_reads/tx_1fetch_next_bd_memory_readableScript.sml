open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_1fetch_next_bd_lemmasTheory;
open tx_bd_queueTheory;
open txInvariantMemoryReadsTheory;
open txTheory;
open txInvariantWellDefinedTheory;
open txInvariantTheory;
open tx_1fetch_next_bdTheory;

val _ = new_theory "tx_1fetch_next_bd_memory_readable";



val TX_fetch_next_bd_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = prove (
  ``!nic nic' READABLE.
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_fetch_next_bd_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_SOP_BD_PA_AND_CPPI_RAM_AND_TX_INVARIANT_BD_QUEUE_FINITE_IMP_EQ_BD_QUEUES_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_fetch_next_bd_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma = prove (
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_BL_GT_ZERO_lemma)) THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma)) THEN
  UNDISCH_TAC ``TX_BL_GT_ZERO (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)`` THEN
  ASM_REWRITE_TAC [TX_BL_GT_ZERO_def, tx_1fetch_next_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);




(******************************************************************************)


  
val TX_fetch_next_bd_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma = prove (
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def] THEN
  DISCH_TAC THEN
  WEAKEN_TAC is_disj THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_NOT_BUFFER_WRAP_OVERFLOW_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [] (SPECL [``nic : nic_state``, ``nic' : nic_state``, ``tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM``] TX_INVARIANT_WELL_DEFINED_IMP_MEMORY_REQUEST_PAs_lemma))) THEN
  UNDISCH_TAC ``¬TX_BUFFER_WRAP_OVERFLOW (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)`` THEN
  REWRITE_TAC [TX_BUFFER_WRAP_OVERFLOW_def, LET_DEF] THEN
  BETA_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `(tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM).sop` THENL
  [
   ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM, wordsTheory.WORD_ADD_0] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
  ]);





(******************************************************************************)



val TX_fetch_next_bd_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma = prove (
  ``!nic nic' READABLE.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_STATE nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [] (SPECL [``nic : nic_state``, ``nic' : nic_state``, ``tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM``] TX_INVARIANT_WELL_DEFINED_IMP_MEMORY_REQUEST_PAs_lemma))) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_fetch_next_bd_MEMORY_READABLE_BD_QUEUE_IMP_MEMORY_READABLE_BD_lemma)) THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_STATE_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE_BD nic.tx.current_bd_pa nic.regs.CPPI_RAM READABLE`` TX_INVARIANT_MEMORY_READABLE_BD_def THEN
  PAT_ASSUM ``let x = y in z`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `(tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM).sop` THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``pa : 32 word`` thm)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



(* Preservation of the complete invariant of the transmission automaton. *)
val TX_fetch_next_bd_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_fetch_next_bd_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic nic' READABLE.
    (nic' = tx_1fetch_next_bd nic) /\
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_fetch_next_bd_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_fetch_next_bd_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_fetch_next_bd_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_fetch_next_bd_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma)) THEN
  ASSUME_TAC(CONJ_ANT_TO_HYP (SPEC_ALL TX_fetch_next_bd_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

