open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_3process_memory_read_reply_lemmasTheory;
open txInvariantWellDefinedTheory;
open tx_invariant_well_defined_lemmasTheory;
open tx_state_lemmasTheory;

val _ = new_theory "tx_3process_memory_read_reply";

val TX_process_memory_read_reply_PRESERVES_NOT_DEAD_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_NOT_DEAD_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_process_memory_read_reply_PRESERVES_BD_QUEUE_FINITE_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_BD_QUEUE_FINITE_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_process_memory_read_reply_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_process_memory_read_reply_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_CURRENT_BD_PA_IN_QUEUE_STATE_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)




val TX_process_memory_read_reply_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_process_memory_read_reply_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_process_memory_read_reply_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma)) THEN
  ASM_REWRITE_TAC []);


(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_3process_memory_read_reply_TX_INVARIANT_IMP_NEXT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NON_MODIFICATION_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_process_memory_read_reply_PRESERVES_CURRENT_BD_STATE_lemma = prove (
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_CURRENT_BD_EOP_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_CURRENT_BD_STATE_def]);


(******************************************************************************)


val TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_NOT_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_CURRENT_BD_PA_IN_QUEUE_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_PRESERVES_CURRENT_BD_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();



