open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_5clear_owner_and_hdp_lemmasTheory;
open txInvariantWellDefinedTheory;
open bd_listTheory;
open tx_state_lemmasTheory;

val _ = new_theory "tx_5clear_owner_and_hdp";





(******************************************************************************)



val TX_clear_owner_and_hdp_PRESERVES_NOT_DEAD_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_NOT_DEAD nic`` TX_INVARIANT_NOT_DEAD_def THEN
  ASM_REWRITE_TAC [TX_INVARIANT_NOT_DEAD_def]);



(******************************************************************************)



val TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_FINITE_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_EMPTY_QUEUE_lemma)) THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  EXISTS_TAC ``[] : 32 word list`` THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma, listTheory.MEM]);



(******************************************************************************)



val TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def] THEN
  REWRITE_TAC [TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def, listTheory.EVERY_DEF]);




(******************************************************************************)



val TX_clear_owner_and_hdp_PRESERVES_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_NOT_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_def]);



(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_CLEARS_CURRENT_BD_PA_SOP_BD_PA_NOT_EXPECTS_SOP_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_def, listTheory.EVERY_DEF]);




(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_NOT_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_lemma)) THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def, listTheory.EVERY_DEF]);




(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def, listTheory.EVERY_DEF]);




(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def] THEN
  REWRITE_TAC [TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  REWRITE_TAC [TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_IMP_NOT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
  PAT_ASSUM ``TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic'`` (fn thm => REWRITE_TAC [thm]) THEN
  PAT_ASSUM ``~TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic'`` (fn thm => REWRITE_TAC [thm]) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def, listTheory.EVERY_DEF]);




(******************************************************************************)




val TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_STATE_lemma = prove (
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_STATE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_EOP_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);




(********************************************************************************)
(******************INVARIANT_PRESERVED_BY_CLEAR_OWNER_AND_HDP********************)
(********************************************************************************)

val TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_NOT_DEAD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def]);

val _ = export_theory();

