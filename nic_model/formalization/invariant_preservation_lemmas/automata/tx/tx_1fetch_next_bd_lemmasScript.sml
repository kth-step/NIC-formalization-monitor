open HolKernel Parse boolLib bossLib;
open helperTactics;
open txTheory;
open tx_transition_definitionsTheory;
open bd_queue_preservation_lemmasTheory;
open txInvariantWellDefinedTheory;
open tx_state_lemmasTheory;
open tx_invariant_well_defined_lemmasTheory;
open tx_state_definitionsTheory;
open tx_bd_queueTheory;
open tx_invariant_memory_reads_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;

val _ = new_theory "tx_1fetch_next_bd_lemmas";

(*
 * Lemma stating which state components the fetch_next_bd transition function
 * does not modify:
 *
 * fetch_next_bd:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 * -nic.tx.current_bd_pa
 * -nic.tx.expects_sop
 *)
val TX_fetch_next_bd_NON_MODIFICATION_lemma = store_thm (
  "TX_fetch_next_bd_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = tx_1fetch_next_bd nic)
    ==>
    (nic'.tx.current_bd_pa = nic.tx.current_bd_pa) /\
    (nic'.tx.sop_bd_pa = nic.tx.sop_bd_pa) /\
    (nic'.tx.expects_sop = nic.tx.expects_sop) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  (fn g =>
   let val case_splits =
     Cases_on `¬BD_LOCATION_DEFINED nic.tx.current_bd_pa` THEN
     Cases_on `¬TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) nic.tx` THEN
     Cases_on `¬TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)`
       val t =
         ASM_REWRITE_TAC [] THEN
         DISCH_TAC THEN
         ASM_REWRITE_TAC [] THEN
         Cases_on `nic` THEN
         REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
         REWRITE_TAC [combinTheory.K_THM] THEN
         REWRITE_TAC [stateTheory.nic_state_accessors]
   in
     (case_splits THENL [t, t, t, t, t, t, t, ALL_TAC]) g
   end) THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT (WEAKEN_TAC (fn term => true)) THEN
   DISCH_TAC THEN
   Cases_on `nic'` THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_accessors] THEN
   RW_ASM_TAC ``x = y`` stateTheory.nic_state_tx THEN
   RW_ASM_TAC ``x = y`` stateTheory.nic_state_tx_fupd THEN
   RW_ASM_TAC ``x = y`` combinTheory.K_THM THEN
   RW_ASM_TAC ``x = y`` stateTheory.nic_state_11 THEN
   REFLECT_ASM_TAC ``P`` THEN
   ASM_REWRITE_TAC [] THEN
   Cases_on `t'` THEN
   Cases_on `t` THEN
   REWRITE_TAC [stateTheory.tx_state_accessors] THEN
   RW_ASM_TAC ``P`` stateTheory.tx_state_fn_updates THEN
   RW_ASM_TAC ``P`` combinTheory.K_THM THEN
   RW_ASM_TAC ``P`` stateTheory.tx_state_11 THEN
   RW_ASM_TAC ``P`` stateTheory.tx_state_accessors THEN
   RW_ASM_TAC ``P`` stateTheory.nic_state_accessors THEN
   ASM_REWRITE_TAC []);

val tx_1fetch_next_bd_PRESERVES_TX_SOP_BD_PA_lemma = store_thm (
  "tx_1fetch_next_bd_PRESERVES_TX_SOP_BD_PA_lemma",
  ``!nic. NIC_DELTA_PRESERVES_TX_SOP_BD_PA tx_1fetch_next_bd nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``tx_1fetch_next_bd nic``] TX_fetch_next_bd_NON_MODIFICATION_lemma)]);

val tx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma = store_thm (
  "tx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma",
  ``!nic. NIC_DELTA_PRESERVES_CPPI_RAM tx_1fetch_next_bd nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``tx_1fetch_next_bd nic``] TX_fetch_next_bd_NON_MODIFICATION_lemma)]);

(*
 * If the following propertis hold in the current state:
 * -the next buffer descriptor is completely located in CPPI_RAM and on a 32-bit
 *  word boundary.
 * -the configuration of the next buffer descriptor is compatible with
 *  the configurations of previously read buffer descriptors, and
 * -the configuration of the next buffer descriptor is internally well-defined,
 *
 * and the NIC fetches the next buffer descriptor, then the NIC will not enter
 * an undefined state.
 *)
val TX_fetch_next_bd_PRESERVES_NOT_DEAD_lemma = store_thm (
  "TX_fetch_next_bd_PRESERVES_NOT_DEAD_lemma",
  ``!nic nic'.
    (nic' = tx_1fetch_next_bd nic) /\
    BD_LOCATION_DEFINED nic.tx.current_bd_pa /\
    TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) nic.tx /\
    TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  UNDISCH_TAC ``nic' = tx_1fetch_next_bd nic`` THEN
  REWRITE_TAC [tx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  Cases_on `nic'` THEN
  REWRITE_TAC [stateTheory.nic_state_tx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_11] THEN
  REWRITE_TAC [stateTheory.nic_state_dead] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma = prove (
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    BD_LOCATION_DEFINED nic.tx.current_bd_pa``,
  GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``tx_bd_queue nic``] TX_INVARIANT_BD_PA_IN_QUEUE_AND_QUEUE_LOCATION_DEFINED_IMP_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs_lemma = prove (
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) nic.tx``,
  GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_lemma = prove (
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic`` TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic`` TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``] TX_INVARIANT_BD_PA_IN_QUEUE_AND_QUEUE_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma = store_thm (
  "TX_INVARIANT_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma",
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    BD_LOCATION_DEFINED nic.tx.current_bd_pa /\
    TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) nic.tx /\
    TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_1fetch_next_bd_IMP_NEXT_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma = store_thm (
  "tx_1fetch_next_bd_IMP_NEXT_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma",
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def, tx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val tx_1fetch_next_bd_IMP_NEXT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma = store_thm (
  "tx_1fetch_next_bd_IMP_NEXT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma",
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_1fetch_next_bd_IMP_NEXT_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma)) THEN
  ASM_REWRITE_TAC [TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_def]);

val TX_INVARIANT_IMP_CURRENT_BD_EOP_lemma = prove (
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM).eop``,
  GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.current_bd_pa``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``] TX_INVARIANT_BD_PA_IN_QUEUE_AND_LINUX_SOP_EOP_MATCH_IMP_TX_INVARIANT_CURRENT_BD_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_IMP_CURRENT_BD_EOP_EQ_CURRENT_BD_PA_CPPI_RAM_EOP_lemma = prove (
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (nic'.tx.current_bd.eop = (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM).eop)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (CONJ (CONJUNCT1 thm) (CONJUNCT2 (CONJUNCT2 thm)))) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [tx_1fetch_next_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_tx_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd]);

val TX_fetch_next_bd_AND_TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_EOP_STATE_lemma = store_thm (
  "TX_fetch_next_bd_AND_TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_EOP_STATE_lemma",
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_EOP_STATE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_IMP_CURRENT_BD_EOP_EQ_CURRENT_BD_PA_CPPI_RAM_EOP_lemma)) THEN
  ASM_REWRITE_TAC []);

(************************)

val TX_fetch_next_bd_CURRENT_BD_NDP_EQ_CURRENT_BD_PA_NDP_lemma = prove (
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (nic'.tx.current_bd.ndp = read_ndp nic.tx.current_bd_pa nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_lemma)) THEN

  ASM_REWRITE_TAC [tx_1fetch_next_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN

  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_tx_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_tx, stateTheory.nic_state_regs] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd_pa] THEN
  REWRITE_TAC [stateTheory.tx_state_sop_packet_length] THEN
  REWRITE_TAC [stateTheory.tx_state_sum_buffer_length] THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd] THEN

  REWRITE_TAC [tx_read_ndp_EQ_read_ndp_lemma]);

val TX_fetch_next_bd_PRESERVES_TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma = store_thm (
  "TX_fetch_next_bd_PRESERVES_TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma",
  ``!nic nic'.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_fetch_next_bd_CURRENT_BD_NDP_EQ_CURRENT_BD_PA_NDP_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_fetch_next_bd_NON_MODIFICATION_lemma)) THEN
  REWRITE_TAC [CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def] THEN
  ASM_REWRITE_TAC []);










val TX_MEMBER_OF_WELL_DEFINED_BD_QUEUE_IMP_BL_GT_ZERO_lemma = store_thm (
  "TX_MEMBER_OF_WELL_DEFINED_BD_QUEUE_IMP_BL_GT_ZERO_lemma",
  ``!q bd_pa CPPI_RAM.
    MEM bd_pa q /\
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM
    ==>
    TX_BL_GT_ZERO (tx_read_bd bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def, listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : 32 word`` thm))) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED bd_pa CPPI_RAM`` TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED_def THEN
  RW_ASM_TAC ``TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd bd_pa CPPI_RAM)`` TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_def THEN
  ASM_REWRITE_TAC []);


val TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_BL_GT_ZERO_lemma = store_thm (
  "TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_BL_GT_ZERO_lemma",
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_BL_GT_ZERO (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic`` TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic`` TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``] TX_MEMBER_OF_WELL_DEFINED_BD_QUEUE_IMP_BL_GT_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);







val TX_MEMBER_OF_WELL_DEFINED_BD_QUEUE_IMP_NOT_BUFFER_WRAP_OVERFLOW_lemma = store_thm (
  "TX_MEMBER_OF_WELL_DEFINED_BD_QUEUE_IMP_NOT_BUFFER_WRAP_OVERFLOW_lemma",
  ``!q bd_pa CPPI_RAM.
    MEM bd_pa q /\
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM
    ==>
    ~TX_BUFFER_WRAP_OVERFLOW (tx_read_bd bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def, listTheory.EVERY_MEM] THEN
  BETA_TAC THEN  
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : 32 word`` thm))) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED bd_pa CPPI_RAM`` TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED_def THEN
  RW_ASM_TAC ``TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd bd_pa CPPI_RAM)`` TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_def THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_NOT_BUFFER_WRAP_OVERFLOW_lemma = store_thm (
  "TX_INVARIANT_WELL_DEFINED_IMP_CURRENT_BD_PA_NOT_BUFFER_WRAP_OVERFLOW_lemma",
  ``!nic.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    ~TX_BUFFER_WRAP_OVERFLOW (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic`` TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic`` TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  MATCH_MP_TAC TX_MEMBER_OF_WELL_DEFINED_BD_QUEUE_IMP_NOT_BUFFER_WRAP_OVERFLOW_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_WELL_DEFINED_IMP_MEMORY_REQUEST_PAs_lemma = store_thm (
  "TX_INVARIANT_WELL_DEFINED_IMP_MEMORY_REQUEST_PAs_lemma",
  ``!nic nic' bd.
    TX_STATE_FETCH_NEXT_BD nic /\
    (nic' = tx_1fetch_next_bd nic) /\
    (bd = tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (nic'.tx.pa_of_next_memory_buffer_byte = if bd.sop then bd.bp + bd.bo else bd.bp) /\
    (nic'.tx.number_of_buffer_bytes_left_to_request = bd.bl)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [tx_1fetch_next_bd_def, LET_DEF] THEN
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

val TX_fetch_next_bd_MEMORY_READABLE_BD_QUEUE_IMP_MEMORY_READABLE_BD_lemma = store_thm (
  "TX_fetch_next_bd_MEMORY_READABLE_BD_QUEUE_IMP_MEMORY_READABLE_BD_lemma",
  ``!nic READABLE.
    TX_STATE_FETCH_NEXT_BD nic /\
    TX_INVARIANT_WELL_DEFINED nic /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD nic.tx.current_bd_pa nic.regs.CPPI_RAM READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_FETCH_NEXT_BD_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  MATCH_MP_TAC TX_BD_PA_MEMBER_READABLE_BD_QUEUE_IMP_BD_PA_ADDRESS_READABLE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val tx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def = Define `
  tx_1fetch_next_bd_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val tx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "tx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
      tx_1fetch_next_bd
      nic
      tx_1fetch_next_bd_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [tx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``tx_1fetch_next_bd nic``] TX_fetch_next_bd_NON_MODIFICATION_lemma)]);

val tx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma = store_thm (
  "tx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    tx_1fetch_next_bd_cppi_ram_write_step_bd_pas
    (tx_bd_queue nic)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val tx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "tx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
      tx_1fetch_next_bd_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [tx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [listTheory.MEM]);

val tx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "tx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      tx_1fetch_next_bd
      nic
      tx_1fetch_next_bd_cppi_ram_write_step_bd_pas
      (tx_bd_queue nic)``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [tx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [tx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val tx_1fetch_next_bd_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_1fetch_next_bd_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic q.
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM (tx_1fetch_next_bd nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ``tx_1fetch_next_bd_cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [tx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val _ = export_theory();
