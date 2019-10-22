open HolKernel Parse boolLib bossLib;
open helperTactics;
open txTheory;
open tx_state_definitionsTheory;
open txInvariantWellDefinedTheory;
open CPPI_RAMTheory;
open bd_queueTheory;
open tx_state_lemmasTheory;
open tx_invariant_well_defined_lemmasTheory;
open set_eoq_lemmasTheory;
open tx_bd_queueTheory;
open clear_own_lemmasTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open bd_listTheory;
open bdTheory;
open txInvariantMemoryReadsTheory;
open tx_invariant_memory_reads_lemmasTheory;
open tx_transition_definitionsTheory;

val _ = new_theory "tx_4post_process_lemmas";

val TX_post_process_RX_BUFFER_OFFSET_NON_MODIFICATION_lemma = store_thm (
  "TX_post_process_RX_BUFFER_OFFSET_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [tx_4post_process_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val TX_post_process_OTHER_AUTOMATA_NON_MODIFICATION_lemma = store_thm (
  "TX_post_process_OTHER_AUTOMATA_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [tx_4post_process_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors]);

val TX_post_process_TX_FIELDs_NON_MODIFICATION_lemma = store_thm (
  "TX_post_process_TX_FIELDs_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    (nic'.tx.current_bd.eop = nic.tx.current_bd.eop) /\
    (nic'.tx.current_bd.ndp = nic.tx.current_bd.ndp)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [tx_4post_process_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

(*
 * The following is a list of which state components that the transmission
 * invariant depends on (nic.dead, nic.tx.sop_bd_pa, nic.regs.CPPI_RAM,
 * nic.tx.current_bd_pa, nic.tx.expects_sop, nic.tx.current_bd), and that
 * post_process does not modify:
 * -nic.dead
 * -nic.tx.current_bd
 *)
val TX_post_process_NON_MODIFICATION_lemma = store_thm (
  "TX_post_process_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.tx.current_bd.eop = nic.tx.current_bd.eop) /\
    (nic'.tx.current_bd.ndp = nic.tx.current_bd.ndp) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_RX_BUFFER_OFFSET_NON_MODIFICATION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_OTHER_AUTOMATA_NON_MODIFICATION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_TX_FIELDs_NON_MODIFICATION_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_post_process_LAST_BD_IMP_NEXT_STATE_clear_owner_and_hdp_lemma = store_thm (
  "TX_post_process_LAST_BD_IMP_NEXT_STATE_clear_owner_and_hdp_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    TX_STATE_CLEAR_OWNER_AND_HDP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def, TX_STATE_CLEAR_OWNER_AND_HDP_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates, combinTheory.K_THM, stateTheory.tx_state_state]);

val TX_post_process_LAST_BD_SET_EOQ_lemma = prove (
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    (nic'.regs.CPPI_RAM = set_eoq nic.regs.CPPI_RAM nic.tx.current_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs_fupd, stateTheory.nic_state_tx_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_regs] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_CPPI_RAM_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_CPPI_RAM]);

val TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma = prove (
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    (nic'.regs.CPPI_RAM = clear_own nic.regs.CPPI_RAM nic.tx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs_fupd, stateTheory.nic_state_tx_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_regs] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_CPPI_RAM_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_CPPI_RAM]);

val TX_post_process_LAST_BD_NON_MODIFICATION_SOP_BD_PA_lemma = store_thm (
  "TX_post_process_LAST_BD_NON_MODIFICATION_SOP_BD_PA_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    (nic.tx.sop_bd_pa = nic'.tx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``nic' = tx_4post_process nic`` tx_4post_process_def THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_state_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_sop_bd_pa]);

val TX_post_process_LAST_BD_NON_MODIFICATION_CURRENT_BD_PA_lemma = store_thm (
  "TX_post_process_LAST_BD_NON_MODIFICATION_CURRENT_BD_PA_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    (nic.tx.current_bd_pa = nic'.tx.current_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``nic' = tx_4post_process nic`` tx_4post_process_def THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_state_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd_pa]);

val TX_post_process_NOT_LAST_BD_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_lemma = prove (
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic)
    ==>
    (nic'.tx.sop_bd_pa = nic.tx.current_bd.ndp)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs_fupd, stateTheory.nic_state_tx_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd_pa_fupd, stateTheory.tx_state_sop_bd_pa_fupd, stateTheory.tx_state_expects_sop_fupd, stateTheory.tx_state_state_fupd, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_sop_bd_pa, stateTheory.tx_state_current_bd]);

val TX_post_process_NOT_LAST_BD_IMP_SOP_BD_PA_NDP_EQ_NEXT_STATE_SOP_BD_PA_lemma = prove (
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = nic'.tx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_STATE_def] THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def] THEN
  REWRITE_TAC [CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def] THEN
  REWRITE_TAC [LAST_BD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [LAST_BD_def] (SPEC_ALL TX_post_process_NOT_LAST_BD_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_lemma))) THEN
  ASM_RW_ASM_TAC ``TX_STATE_POST_PROCESS nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``nic.tx.current_bd.ndp <> 0w`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``nic.tx.current_bd.ndp = read_ndp nic.tx.current_bd_pa nic.regs.CPPI_RAM`` ``nic'.tx.sop_bd_pa = nic.tx.current_bd.ndp`` THEN
  ASM_RW_ASM_TAC ``nic.tx.current_bd_pa = nic.tx.sop_bd_pa`` ``nic'.tx.sop_bd_pa = read_ndp nic.tx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val TX_STATE_POST_PROCESS_SUBINVARIANT_NOT_ZERO_CURRENT_BD_NDP_IN_TX_BD_QUEUE_lemma = store_thm (
  "TX_STATE_POST_PROCESS_SUBINVARIANT_NOT_ZERO_CURRENT_BD_NDP_IN_TX_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_INVARIANT_CURRENT_BD_STATE nic /\
    nic.tx.current_bd.ndp <> 0w
    ==>
    MEM nic.tx.current_bd.ndp (tx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NON_LAST_IN_Q_THEN_NEXT_IN_Q_lemma THEN
  EXISTS_TAC ``nic.tx.sop_bd_pa`` THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  EXISTS_TAC ``nic.tx.current_bd_pa`` THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_STATE nic`` TX_INVARIANT_CURRENT_BD_STATE_def THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT2 thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic`` TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def THEN
  RW_ASM_TAC ``P ==> Q`` BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def THEN
  KEEP_ASM_RW_ASM_TAC ``TX_STATE_POST_PROCESS nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  RW_ASM_TAC ``CURRENT_BD_NDP_EQ_CPPI_RAM_NDP nic`` CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def THEN
  KEEP_ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [GSYM TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma]);

val TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``TX_STATE_POST_PROCESS nic`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [thm] (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic`` TX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_bd_queueTheory.TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_PRESERVED_set_eoq_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_NON_MODIFICATION_SOP_BD_PA_lemma)) THEN
  ASM_RW_ASM_TAC ``nic.tx.sop_bd_pa = nic'.tx.sop_bd_pa`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic' : nic_state``, ``tx_bd_queue nic``] TX_BD_QUEUE_IMP_tx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);




val TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma)) THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic`` TX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_bd_queueTheory.TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``tx_bd_queue nic``, ``nic.tx.sop_bd_pa``, `` nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_PRESERVED_clear_own_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_SOP_BD_PA_HEAD_BD_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  KEEP_ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::t`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` THEN
  KEEP_ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::t`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.sop_bd_pa``, ``t : 32 word list``, ``nic.tx.sop_bd_pa``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_NON_EMPTY_IMP_EQ_NDP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic.tx.sop_bd_pa``, ``t : 32 word list``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_IMP_TL_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = read_ndp nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``read_ndp nic.tx.sop_bd_pa nic'.regs.CPPI_RAM = read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM`` ``BD_QUEUE t (read_ndp nic.tx.sop_bd_pa nic'.regs.CPPI_RAM) nic'.regs.CPPI_RAM`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_SOP_BD_PA_NDP_EQ_NEXT_STATE_SOP_BD_PA_lemma)) THEN
  ASM_RW_ASM_TAC ``read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = nic'.tx.sop_bd_pa`` ``BD_QUEUE t (read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM) nic'.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (GSYM (SPECL [``nic' : nic_state``, ``t : 32 word list``] TX_BD_QUEUE_IMP_tx_bd_queue_lemma))) THEN
  ASM_RW_ASM_TAC ``t = tx_bd_queue nic'`` ``tx_bd_queue nic = nic.tx.sop_bd_pa::t`` THEN
  ASM_REWRITE_TAC []);

val TX_post_process_NOT_LAST_BD_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    tx_bd_queue nic' <> []``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  CCONTR_TAC THEN
  RW_ASM_TAC ``~~P`` boolTheory.NOT_CLAUSES THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic' = []`` ``tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic'`` THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic`` TX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = [nic.tx.sop_bd_pa]`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM`` THEN
  RW_ASM_TAC ``BD_QUEUE [h] s m`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_SOP_BD_PA_NDP_EQ_NEXT_STATE_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_lemma)) THEN
  ASM_RW_ASM_TAC ``read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = nic'.tx.sop_bd_pa`` ``read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = 0w`` THEN
  ASM_RW_ASM_TAC ``nic'.tx.sop_bd_pa = nic.tx.current_bd.ndp`` ``nic'.tx.sop_bd_pa = 0w`` THEN
  RW_ASM_TAC ``nic.tx.current_bd.ndp = 0w`` (GSYM LAST_BD_def) THEN
  ASM_RW_ASM_TAC ``LAST_BD nic.tx.current_bd`` ``~LAST_BD nic.tx.current_bd`` THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

(*
 * END OF GENERAL LEMMAS
 *)



(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val tx_4post_process_cppi_ram_write_step_bd_pas_def = Define `
  tx_4post_process_cppi_ram_write_step_bd_pas nic =
  if LAST_BD nic.tx.current_bd then
    [(set_eoq, nic.tx.current_bd_pa)]
  else
    [(clear_own, nic.tx.sop_bd_pa)]`;

val tx_4post_process_WRITES_CPPI_RAM_lemma = store_thm (
  "tx_4post_process_WRITES_CPPI_RAM_lemma",
  ``!nic.
    ((tx_4post_process nic).regs.CPPI_RAM =
     cppi_ram_write nic.regs.CPPI_RAM (tx_4post_process_cppi_ram_write_step_bd_pas nic))``,
  GEN_TAC THEN
  REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val tx_4post_process_cppi_ram_write_step_bd_pas_LAST_BD_EQ_BD_PAs_lemma = store_thm (
  "tx_4post_process_cppi_ram_write_step_bd_pas_LAST_BD_EQ_BD_PAs_lemma",
  ``!nic.
    LAST_BD nic.tx.current_bd
    ==>
    (MAP SND (tx_4post_process_cppi_ram_write_step_bd_pas nic) = [nic.tx.current_bd_pa])``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val tx_4post_process_cppi_ram_write_step_bd_pas_NOT_LAST_BD_EQ_BD_PAs_lemma = store_thm (
  "tx_4post_process_cppi_ram_write_step_bd_pas_NOT_LAST_BD_EQ_BD_PAs_lemma",
  ``!nic.
    ~LAST_BD nic.tx.current_bd
    ==>
    (MAP SND (tx_4post_process_cppi_ram_write_step_bd_pas nic) = [nic.tx.sop_bd_pa])``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val tx_4post_process_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "tx_4post_process_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
      tx_4post_process
      nic
      (tx_4post_process_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [tx_4post_process_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val tx_4post_process_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma = store_thm (
  "tx_4post_process_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (tx_4post_process_cppi_ram_write_step_bd_pas nic)
    (tx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  Cases_on `LAST_BD nic.tx.current_bd` THENL
  [
   ASM_REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
   GEN_TAC THEN
   REWRITE_TAC [listTheory.MEM] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
   GEN_TAC THEN
   REWRITE_TAC [listTheory.MEM] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val tx_4post_process_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "tx_4post_process_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
      (tx_4post_process_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [listTheory.MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THENL
  [
   REWRITE_TAC [set_eoq_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma] THEN
   REWRITE_TAC [set_eoq_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma]
   ,
   REWRITE_TAC [clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma] THEN
   REWRITE_TAC [clear_own_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma]
  ]);

val tx_4post_process_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "tx_4post_process_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      tx_4post_process
      nic
      (tx_4post_process_cppi_ram_write_step_bd_pas nic)
      (tx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_4post_process_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [tx_4post_process_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(* Lemma useful to show that the transmission automaton does not modify anything
   outside its own queue. *)
val tx_4post_process_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_4post_process_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic q.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM (tx_4post_process nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ``tx_4post_process_cppi_ram_write_step_bd_pas nic : cppi_ram_write_step_bd_pas_type`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_4post_process_WRITES_FIELDs_NOT_NDP_OF_BD_AT_SOP_BD_PA_lemma = store_thm (
  "tx_4post_process_WRITES_FIELDs_NOT_NDP_OF_BD_AT_SOP_BD_PA_lemma",
  ``!nic.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      tx_4post_process
      nic
      (tx_4post_process_cppi_ram_write_step_bd_pas nic)
      [nic.tx.sop_bd_pa]``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_4post_process_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  ASM_REWRITE_TAC [tx_4post_process_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN  
  REWRITE_TAC [tx_4post_process_cppi_ram_write_step_bd_pas_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [listTheory.MAP] THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic`` TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);


(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)




(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_BD_QUEUE_FINITE
 *)

val TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic`` TX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN  
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_PRESERVED_set_eoq_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_NON_MODIFICATION_SOP_BD_PA_lemma)) THEN
  ASM_RW_ASM_TAC ``nic.tx.sop_bd_pa = nic'.tx.sop_bd_pa`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);



(***NOT LAST****)



val TX_post_process_NOT_LAST_BD_IMP_BD_QUEUE_IN_PRESTATE_BD_QUEUE_IN_POST_STATE_lemma = prove (
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic`` TX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``tx_bd_queue nic``, ``nic.tx.sop_bd_pa``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_PRESERVED_clear_own_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_IMP_BD_QUEUE_lemma = prove (
  ``!nic.
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM``,
  GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def, TX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_FINITE_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_FINITE_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_IMP_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_BD_QUEUE_IN_PRESTATE_BD_QUEUE_IN_POST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_SOP_BD_PA_NDP_EQ_NEXT_STATE_SOP_BD_PA_lemma)) THEN
  KEEP_ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic'`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic'`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.sop_bd_pa``, ``tx_bd_queue nic'``, ``nic.tx.sop_bd_pa``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_NON_EMPTY_IMP_EQ_NDP_lemma)) THEN
  RW_ASM_TAC ``BD_QUEUE (nic.tx.sop_bd_pa::tx_bd_queue nic') nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = read_ndp nic.tx.sop_bd_pa nic'.regs.CPPI_RAM`` ``read_ndp nic.tx.sop_bd_pa nic.regs.CPPI_RAM = nic'.tx.sop_bd_pa`` THEN
  ASM_RW_ASM_TAC ``read_ndp nic.tx.sop_bd_pa nic'.regs.CPPI_RAM = nic'.tx.sop_bd_pa`` ``BD_QUEUE (tx_bd_queue nic') (read_ndp nic.tx.sop_bd_pa nic'.regs.CPPI_RAM) nic'.regs.CPPI_RAM`` THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  EXISTS_TAC ``tx_bd_queue nic'`` THEN
  ASM_REWRITE_TAC []);










(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH.
 *)

val BD_WRITE_PRESERVES_set_eoq_LINUX_BD_SOP_EOP_lemma = store_thm (
  "BD_WRITE_PRESERVES_set_eoq_LINUX_BD_SOP_EOP_lemma",
  ``BD_WRITE_PRESERVES_BD_PROPERTY set_eoq TX_LINUX_BD_SOP_EOP``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PRESERVED_def, TX_LINUX_BD_SOP_EOP_def] THEN
  REWRITE_TAC [TX_LINUX_BD_SOP_def, TX_LINUX_BD_EOP_def] THEN
  REWRITE_TAC [set_eoq_PRESERVES_SOP_lemma] THEN
  REWRITE_TAC [set_eoq_PRESERVES_EOP_lemma]);

val BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_LINUX_BD_SOP_EOP_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_LINUX_BD_SOP_EOP_lemma",
  ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY set_eoq TX_LINUX_BD_SOP_EOP``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_PRESERVES_set_eoq_LINUX_BD_SOP_EOP_lemma] THEN
  REWRITE_TAC [BD_WRITE_set_eoq_lemma]);

val NOT_OVERLAPPING_CPPI_RAM_BD_QUEUE_set_eoq_PRESERVES_LINUX_BD_SOP_EOP_lemma = store_thm (
  "NOT_OVERLAPPING_CPPI_RAM_BD_QUEUE_set_eoq_PRESERVES_LINUX_BD_SOP_EOP_lemma",
  ``!q bd_pa CPPI_RAM CPPI_RAM'.
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    (CPPI_RAM' = set_eoq CPPI_RAM bd_pa) /\
    MEM bd_pa q
    ==>
    BD_QUEUE_PRESERVED TX_LINUX_BD_SOP_EOP q CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_LINUX_BD_SOP_EOP_lemma] (SPEC_ALL (SPECL [``set_eoq``, ``TX_LINUX_BD_SOP_EOP``] BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma)))) THEN
  ASM_REWRITE_TAC []);

val NOT_OVERLAPPING_CPPI_RAM_BD_QUEUE_set_eoq_PRESERVES_LINUX_BD_SOP_EOP_lemma = store_thm (
  "NOT_OVERLAPPING_CPPI_RAM_BD_QUEUE_set_eoq_PRESERVES_LINUX_BD_SOP_EOP_lemma",
  ``!q bd_pa CPPI_RAM CPPI_RAM'.
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    TX_LINUX_BD_QUEUE_SOP_EOP_MATCH q CPPI_RAM /\
    (CPPI_RAM' = set_eoq CPPI_RAM bd_pa) /\
    MEM bd_pa q
    ==>
    TX_LINUX_BD_QUEUE_SOP_EOP_MATCH q CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NOT_OVERLAPPING_CPPI_RAM_BD_QUEUE_set_eoq_PRESERVES_LINUX_BD_SOP_EOP_lemma)) THEN
  RW_ASM_TAC ``TX_LINUX_BD_QUEUE_SOP_EOP_MATCH q CPPI_RAM`` TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_LINUX_BD_SOP_EOP_DEPENDS_ONLY_ON_BD_lemma] (SPECL [``TX_LINUX_BD_SOP_EOP``, ``q : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``, ``CPPI_RAM' : 13 word -> 8 word``] BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma))) THEN
  ASM_REWRITE_TAC [TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def]);

val TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] NOT_OVERLAPPING_CPPI_RAM_BD_QUEUE_set_eoq_PRESERVES_LINUX_BD_SOP_EOP_lemma)) THEN
  REFLECT_ASM_TAC ``tx_bd_queue nic' = tx_bd_queue nic`` THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = tx_bd_queue nic'`` ``TX_LINUX_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic'.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val BD_WRITE_PRESERVES_clear_own_LINUX_BD_SOP_EOP_lemma = store_thm (
  "BD_WRITE_PRESERVES_clear_own_LINUX_BD_SOP_EOP_lemma",
  ``BD_WRITE_PRESERVES_BD_PROPERTY clear_own TX_LINUX_BD_SOP_EOP``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PRESERVED_def, TX_LINUX_BD_SOP_EOP_def] THEN
  REWRITE_TAC [TX_LINUX_BD_SOP_def, TX_LINUX_BD_EOP_def] THEN
  REWRITE_TAC [clear_own_PRESERVES_SOP_lemma] THEN
  REWRITE_TAC [clear_own_PRESERVES_EOP_lemma]);

val BD_WRITE_PRESERVES_BD_QUEUE_clear_own_LINUX_BD_SOP_EOP_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_QUEUE_clear_own_LINUX_BD_SOP_EOP_lemma",
  ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY clear_own TX_LINUX_BD_SOP_EOP``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_PRESERVES_clear_own_LINUX_BD_SOP_EOP_lemma] THEN
  REWRITE_TAC [BD_WRITE_clear_own_lemma]);

val TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_WRITE_PRESERVES_BD_QUEUE_clear_own_LINUX_BD_SOP_EOP_lemma] (SPECL [``clear_own``, ``TX_LINUX_BD_SOP_EOP``, ``tx_bd_queue nic``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma))) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def THEN
  RW_ASM_TAC ``TX_LINUX_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_LINUX_BD_SOP_EOP_DEPENDS_ONLY_ON_BD_lemma] (SPECL [``TX_LINUX_BD_SOP_EOP``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = h::t`` ``EVERY (λbd_pa. TX_LINUX_BD_SOP_EOP bd_pa nic'.regs.CPPI_RAM) (tx_bd_queue nic)`` THEN
  RW_ASM_TAC ``EVERY P (h::t)`` listTheory.EVERY_DEF THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def, TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def, TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def]);


















(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY.
 *)

val TX_post_process_LAST_BD_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    tx_bd_queue nic' <> []``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  COPY_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic`` TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (REWRITE_RULE [NOT_TX_BD_QUEUE_EMPTY_def] (UNDISCH thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);


val TX_post_process_NOT_LAST_BD_PRESERVES_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_def, NOT_TX_BD_QUEUE_EMPTY_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC []);








(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA.
 *)

val TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def, TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs, stateTheory.nic_state_tx] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates, combinTheory.K_THM, stateTheory.tx_state_current_bd] THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd_pa, stateTheory.tx_state_sop_bd_pa]);






(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE.
 *)

val tx_4post_process_LAST_BD_PRESERVES_CURRENT_BD_PA_SOP_lemma = store_thm (
  "tx_4post_process_LAST_BD_PRESERVES_CURRENT_BD_PA_SOP_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    ((tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM).sop =
     (tx_read_bd nic'.tx.current_bd_pa nic'.regs.CPPI_RAM).sop)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_NON_MODIFICATION_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [set_eoq_PRESERVES_SOP_lemma]);

val tx_4post_process_LAST_BD_PRESERVES_EXPECTS_SOP_lemma = store_thm (
  "tx_4post_process_LAST_BD_PRESERVES_EXPECTS_SOP_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    (nic'.tx.expects_sop = nic.tx.expects_sop)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val tx_4post_process_LAST_BD_PRESERVES_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma = store_thm (
  "tx_4post_process_LAST_BD_PRESERVES_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic`` TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_NOT_BD_QUEUE_EMPTY nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) nic.tx`` TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_LAST_BD_PRESERVES_CURRENT_BD_PA_SOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_LAST_BD_PRESERVES_EXPECTS_SOP_lemma)) THEN
  ASM_REWRITE_TAC [TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP_def]);
















val TX_post_process_NOT_LAST_BD_IMP_NEXT_HEAD_MEMBER_OF_NEXT_QUEUE_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_IMP_NEXT_HEAD_MEMBER_OF_NEXT_QUEUE_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    MEM nic'.tx.sop_bd_pa (tx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic'`` TX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q nic.tx.sop_bd_pa nic.regs.CPPI_RAM`` TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma THEN
  Cases_on `tx_bd_queue nic'` THENL
  [
   RW_ASM_TAC ``[] <> []`` boolTheory.REFL_CLAUSE THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``nic'.tx.sop_bd_pa``, ``t : 32 word list``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val TX_MEMBER_OF_BD_QUEUE_SOP_EOP_MATCH_IMP_LINUX_SOP_lemma = store_thm (
  "TX_MEMBER_OF_BD_QUEUE_SOP_EOP_MATCH_IMP_LINUX_SOP_lemma",
  ``!nic bd_pa.
    TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic.regs.CPPI_RAM /\
    MEM bd_pa (tx_bd_queue nic)
    ==>
    TX_LINUX_BD_SOP bd_pa nic.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def] THEN
  REWRITE_TAC [TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [TX_LINUX_BD_SOP_EOP_def] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : 32 word`` thm))) THEN
  ASM_REWRITE_TAC []);

val TX_post_process_INVARIANT_IMP_NEXT_CURRENT_BD_PA_SOP_lemma = store_thm (
  "TX_post_process_INVARIANT_IMP_NEXT_CURRENT_BD_PA_SOP_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    (tx_read_bd nic'.tx.current_bd_pa nic'.regs.CPPI_RAM).sop``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_NEXT_HEAD_MEMBER_OF_NEXT_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_SOP_EOP_MATCH_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic'.tx.sop_bd_pa``] TX_MEMBER_OF_BD_QUEUE_SOP_EOP_MATCH_IMP_LINUX_SOP_lemma)) THEN
  RW_ASM_TAC ``TX_LINUX_BD_SOP a m`` TX_LINUX_BD_SOP_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic'`` TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def THEN
  REFLECT_ASM_TAC ``nic'.tx.current_bd_pa = nic'.tx.sop_bd_pa`` THEN
  ASM_RW_ASM_TAC ``nic'.tx.sop_bd_pa = nic'.tx.current_bd_pa`` ``(tx_read_bd nic'.tx.sop_bd_pa nic'.regs.CPPI_RAM).sop`` THEN
  ASM_REWRITE_TAC []);

val TX_post_process_INVARIANT_IMP_NEXT_STATE_EXPECTS_SOP_lemma = store_thm (
  "TX_post_process_INVARIANT_IMP_NEXT_STATE_EXPECTS_SOP_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    nic'.tx.expects_sop``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs, stateTheory.nic_state_tx, stateTheory.nic_state_fn_updates, combinTheory.K_THM] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates, combinTheory.K_THM, stateTheory.tx_state_current_bd, stateTheory.tx_state_expects_sop]);

val TX_post_process_INVARIANT_IMP_NEXT_STATE_EXPECTS_SOP_lemma = store_thm (
  "TX_post_process_INVARIANT_IMP_NEXT_STATE_EXPECTS_SOP_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_INVARIANT_IMP_NEXT_CURRENT_BD_PA_SOP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_INVARIANT_IMP_NEXT_STATE_EXPECTS_SOP_lemma)) THEN
  REWRITE_TAC [TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_def] THEN
  REWRITE_TAC [TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP_def] THEN
  ASM_REWRITE_TAC []);




(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW.
 *)


val BD_WRITE_PRESERVES_set_eoq_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma = store_thm (
  "BD_WRITE_PRESERVES_set_eoq_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma",
  ``BD_WRITE_PRESERVES_BD_PROPERTY set_eoq TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PRESERVED_def] THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_def] THEN
  REWRITE_TAC [set_eoq_PRESERVES_BL_lemma]);

val BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma",
  ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY set_eoq TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_PRESERVES_set_eoq_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma] THEN
  REWRITE_TAC [BD_WRITE_set_eoq_lemma]);

val BD_WRITE_PRESERVES_clear_own_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma = store_thm (
  "BD_WRITE_PRESERVES_clear_own_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma",
  ``BD_WRITE_PRESERVES_BD_PROPERTY clear_own TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PRESERVED_def] THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_def] THEN
  REWRITE_TAC [clear_own_PRESERVES_BL_lemma]);

val BD_WRITE_PRESERVES_BD_QUEUE_clear_own_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_QUEUE_clear_own_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma",
  ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY clear_own TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_PRESERVES_clear_own_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma] THEN
  REWRITE_TAC [BD_WRITE_clear_own_lemma]);

val TX_post_process_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma] (SPECL [``set_eoq``, ``TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``, ``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma))) THEN
  RW_ASM_TAC ``TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_DEPENDS_ONLY_ON_BD_lemma] (SPECL [``TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``tx_bd_queue nic' = tx_bd_queue nic`` THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = tx_bd_queue nic'`` ``EVERY (λbd_pa. TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW bd_pa nic'.regs.CPPI_RAM) (tx_bd_queue nic)`` THEN
  ASM_REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def]);

val TX_post_process_NOT_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_WRITE_PRESERVES_BD_QUEUE_clear_own_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_lemma] (SPECL [``clear_own``, ``TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``, ``tx_bd_queue nic``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma))) THEN
  RW_ASM_TAC ``TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_DEPENDS_ONLY_ON_BD_lemma] (SPECL [``TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic'`` ``EVERY (λbd_pa. TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW bd_pa nic'.regs.CPPI_RAM) (tx_bd_queue nic)`` THEN
  RW_ASM_TAC ``EVERY (λbd_pa. TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW bd_pa nic'.regs.CPPI_RAM) (nic.tx.sop_bd_pa::tx_bd_queue nic')`` listTheory.EVERY_DEF THEN
  ASM_REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def]);



(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH.
 *)

val BD_WRITE_PRESERVES_set_eoq_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma = store_thm (
  "BD_WRITE_PRESERVES_set_eoq_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma",
  ``BD_WRITE_PRESERVES_BD_PROPERTY set_eoq TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PRESERVED_def] THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_def] THEN
  REWRITE_TAC [set_eoq_PRESERVES_BL_lemma, set_eoq_PRESERVES_PL_lemma]);

val BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma",
  ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY set_eoq TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_PRESERVES_set_eoq_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma] THEN
  REWRITE_TAC [BD_WRITE_set_eoq_lemma]);

val BD_WRITE_PRESERVES_clear_own_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma = store_thm (
  "BD_WRITE_PRESERVES_clear_own_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma",
  ``BD_WRITE_PRESERVES_BD_PROPERTY clear_own TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PRESERVED_def] THEN
  REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_def] THEN
  REWRITE_TAC [clear_own_PRESERVES_BL_lemma, clear_own_PRESERVES_PL_lemma]);

val BD_WRITE_PRESERVES_BD_QUEUE_clear_own_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_QUEUE_clear_own_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma",
  ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY clear_own TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``,
  REWRITE_TAC [BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_PRESERVES_clear_own_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma] THEN
  REWRITE_TAC [BD_WRITE_clear_own_lemma]);

val TX_post_process_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_WRITE_PRESERVES_BD_QUEUE_set_eoq_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma] (SPECL [``set_eoq``, ``TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``, ``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma))) THEN
  RW_ASM_TAC ``TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_DEPENDS_ONLY_ON_BD_lemma] (SPECL [``TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``tx_bd_queue nic' = tx_bd_queue nic`` THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = tx_bd_queue nic'`` ``EVERY (λbd_pa. TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH bd_pa nic'.regs.CPPI_RAM) (tx_bd_queue nic)`` THEN
  ASM_REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def]);

val TX_post_process_NOT_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_WRITE_PRESERVES_BD_QUEUE_clear_own_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_lemma] (SPECL [``clear_own``, ``TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``, ``tx_bd_queue nic``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma))) THEN
  RW_ASM_TAC ``TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic) nic.regs.CPPI_RAM`` TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_DEPENDS_ONLY_ON_BD_lemma] (SPECL [``TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic'`` ``EVERY (λbd_pa. TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH bd_pa nic'.regs.CPPI_RAM) (tx_bd_queue nic)`` THEN
  RW_ASM_TAC ``EVERY (λbd_pa. TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH bd_pa nic'.regs.CPPI_RAM) (nic.tx.sop_bd_pa::tx_bd_queue nic')`` listTheory.EVERY_DEF THEN
  ASM_REWRITE_TAC [TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def]);






(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE.
 *)















val tx_4post_process_NOT_MODIFIES_TX_BD_QUEUE_TAIL_lemma = store_thm (
  "tx_4post_process_NOT_MODIFIES_TX_BD_QUEUE_TAIL_lemma",
  ``!nic t.
    TX_STATE_POST_PROCESS nic /\
    TX_INVARIANT_WELL_DEFINED nic /\
    (tx_bd_queue nic = nic.tx.sop_bd_pa::t)
    ==>
    EQ_BDs t nic.regs.CPPI_RAM (tx_4post_process nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``[nic.tx.sop_bd_pa]`` THEN
  EXISTS_TAC ``tx_4post_process_cppi_ram_write_step_bd_pas nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_WRITES_FIELDs_NOT_NDP_OF_BD_AT_SOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_FINITE nic`` TX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_TX_BD_QUEUE_lemma THEN
  KEEP_ASM_RW_ASM_TAC ``x = y`` ``BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM`` THEN
  KEEP_ASM_RW_ASM_TAC ``x = y`` ``TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic)`` THEN
  ASM_RW_ASM_TAC ``x = y`` ``  TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic.tx.sop_bd_pa::t`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP q`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  RW_ASM_TAC ``BDs_IN_CPPI_RAM q`` BDs_IN_CPPI_RAM_HD_TL_EQ_lemma THEN
  ASM_REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_DEF] THEN
  MATCH_MP_TAC BD_QUEUE_NOT_LIST_OVERLAP_IMP_SINGLETON_LIST_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic.tx.sop_bd_pa`` THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_EQ_TAIL_PRESERVED_lemma = store_thm (
  "TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_EQ_TAIL_PRESERVED_lemma",
  ``!q CPPI_RAM CPPI_RAM'.
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM /\
    EQ_BDs q CPPI_RAM CPPI_RAM'
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REPEAT (PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm)))) THEN
  ASSUME_TAC (GSYM (UNDISCH (SPECL [``e : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] (REWRITE_RULE [TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED_DEPENDS_ONLY_ON_BD_lemma] (SPEC ``TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED`` BD_PROPERTY_DEPENDS_ONLY_ON_BD_def))))) THEN
  ASM_REWRITE_TAC []);

val TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_STATE_lemma = store_thm (
  "TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_STATE_lemma",
  ``!nic.
    TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic /\
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED ((TL o tx_bd_queue) nic) nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def] THEN
  REWRITE_TAC [TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  REWRITE_TAC [TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic : nic_state`` TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_NOT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_IMP_COMPLETE_CONFIGURATION_WELL_DEFINED_STATE_lemma = store_thm (
  "TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_IMP_COMPLETE_CONFIGURATION_WELL_DEFINED_STATE_lemma",
  ``!nic.
    TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic /\
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED (tx_bd_queue nic) nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def] THEN
  REWRITE_TAC [TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  REWRITE_TAC [TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def] THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic : nic_state`` TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_IMP_NOT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_lemma = store_thm (
  "TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_lemma",
  ``!nic t.
    TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic /\
    TX_INVARIANT_WELL_DEFINED nic /\
    (tx_bd_queue nic = nic.tx.sop_bd_pa::t)
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED t nic.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic`` TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT2 thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic`` TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q m`` combinTheory.o_DEF THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q m`` (BETA_CONV ``(λx. TL (tx_bd_queue x)) nic``) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::t`` ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q m`` THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q m`` listTheory.TL THEN
  ASM_REWRITE_TAC []);

val TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_STATE_lemma THEN
  ASSUME_TAC (REWRITE_RULE [GSYM TX_STATE_CLEAR_OWNER_AND_HDP_def] (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_IMP_NEXT_STATE_clear_owner_and_hdp_lemma))) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` TX_STATE_CLEAR_OWNER_AND_HDP_IMP_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``TX_STATE_POST_PROCESS nic`` (GSYM TX_STATE_POST_PROCESS_def) THEN
  COPY_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_SOP_BD_PA_HEAD_BD_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  KEEP_ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::t`` ``tx_bd_queue nic' = tx_bd_queue nic`` THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [listTheory.TL] THEN
  MATCH_MP_TAC TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_EQ_TAIL_PRESERVED_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC tx_4post_process_NOT_MODIFIES_TX_BD_QUEUE_TAIL_lemma THEN
  ASM_REWRITE_TAC []);

val tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_WRITE_CP_lemma = store_thm (
  "tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_WRITE_CP_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
     (nic' = tx_4post_process nic)
    ==>
    TX_STATE_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_4post_process_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates, combinTheory.K_THM, stateTheory.tx_state_state]);

val tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma = store_thm (
  "tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
     (nic' = tx_4post_process nic)
    ==>
    TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC [TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_def, TX_STATE_WRITE_CP_def]);

val TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_IMP_COMPLETE_CONFIGURATION_WELL_DEFINED_STATE_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma)) THEN
  PAT_ASSUM ``TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic'`` (fn thm => ASSUME_TAC thm THEN REWRITE_TAC [thm]) THEN
  MATCH_MP_TAC TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_EQ_TAIL_PRESERVED_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  CONJ_TAC THENL
  [
   MATCH_MP_TAC TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_IMP_TAIL_CONFIGURATION_WELL_DEFINED_lemma THEN
   RW_ASM_TAC ``TX_STATE_POST_PROCESS nic`` (GSYM TX_STATE_POST_PROCESS_def) THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma)) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC tx_4post_process_NOT_MODIFIES_TX_BD_QUEUE_TAIL_lemma THEN
   RW_ASM_TAC ``TX_STATE_POST_PROCESS nic`` (GSYM TX_STATE_POST_PROCESS_def) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);




(*
 * LEMMAS FOR PROVING PRESERVATION OF TX_INVARIANT_CURRENT_BD_STATE.
 *)

val TX_post_process_PRESERVES_CURRENT_BD_EOP_STATE_lemma = store_thm (
  "TX_post_process_PRESERVES_CURRENT_BD_EOP_STATE_lemma",
  ``!nic nic'.
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_NON_MODIFICATION_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_STATE nic`` TX_INVARIANT_CURRENT_BD_STATE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_EOP_STATE nic`` TX_INVARIANT_CURRENT_BD_EOP_STATE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_CURRENT_BD_EOP_STATE_def]);

val TX_post_process_NOT_LAST_BD_IMP_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_IMP_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    (nic' = tx_4post_process nic)
    ==>
    ~BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def, boolTheory.DE_MORGAN_THM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_post_process_NON_MODIFICATION_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_IMP_NEXT_STATE_clear_owner_and_hdp_lemma)) THEN
  RW_ASM_TAC ``TX_STATE_CLEAR_OWNER_AND_HDP nic'`` TX_STATE_CLEAR_OWNER_AND_HDP_def THEN
  REWRITE_TAC [TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def] THEN
  REWRITE_TAC [TX_STATE_PROCESS_MEMORY_READ_REPLY_def] THEN
  REWRITE_TAC [TX_STATE_POST_PROCESS_def] THEN
  ASM_REWRITE_TAC [GSYM stateTheory.tx_abstract_state_distinct]);

val TX_post_process_LAST_BD_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (hd (IMP_CANON (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma)))))) THEN
  ASM_REWRITE_TAC []);

val TX_post_process_LAST_BD_PRESERVES_CURRENT_BD_STATE_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_CURRENT_BD_STATE_lemma",
  ``!nic nic'.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_PRESERVES_CURRENT_BD_EOP_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_CURRENT_BD_STATE_def]);

val TX_post_process_NOT_LAST_BD_IMP_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_IMP_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
     (nic' = tx_4post_process nic)
    ==>
    ~BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def, boolTheory.DE_MORGAN_THM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (REWRITE_RULE [TX_STATE_WRITE_CP_def] tx_4post_process_NOT_LAST_BD_IMP_NEXT_TX_STATE_WRITE_CP_lemma))) THEN
  REWRITE_TAC [TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def] THEN
  REWRITE_TAC [TX_STATE_PROCESS_MEMORY_READ_REPLY_def] THEN
  REWRITE_TAC [TX_STATE_POST_PROCESS_def] THEN
  ASM_REWRITE_TAC [GSYM stateTheory.tx_abstract_state_distinct]);

val TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_IMP_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def]);

val TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_STATE_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_STATE_lemma",
  ``!nic nic'.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_PRESERVES_CURRENT_BD_EOP_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_CURRENT_BD_STATE_def]);





val TX_post_process_NEXT_STATE_NEQ_lemma = store_thm (
  "TX_post_process_NEXT_STATE_NEQ_lemma",
  ``!nic nic'.
    (nic' = tx_4post_process nic)
    ==>
    ~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic' /\
    ~TX_STATE_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def, TX_STATE_PROCESS_MEMORY_READ_REPLY_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  REWRITE_TAC [tx_4post_process_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `LAST_BD b'` THEN
  ASM_REWRITE_TAC [stateTheory.nic_state_tx, stateTheory.tx_state_state, GSYM stateTheory.tx_abstract_state_distinct]);


val BD_AP_WRITE_PRESERVES_set_eoq_MEMORY_READABLE_BD_lemma = store_thm (
  "BD_AP_WRITE_PRESERVES_set_eoq_MEMORY_READABLE_BD_lemma",
  ``!READABLE.
    BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY set_eoq TX_INVARIANT_MEMORY_READABLE_BD READABLE``,
  GEN_TAC THEN
  REWRITE_TAC [BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_set_eoq_lemma] THEN
  REWRITE_TAC [BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_AP_PRESERVED_def] THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_BD_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [set_eoq_PRESERVES_SOP_lemma, set_eoq_PRESERVES_BP_lemma] THEN
  REWRITE_TAC [set_eoq_PRESERVES_BO_lemma, set_eoq_PRESERVES_BL_lemma]);

val BD_AP_WRITE_PRESERVES_clear_own_MEMORY_READABLE_BD_lemma = store_thm (
  "BD_AP_WRITE_PRESERVES_clear_own_MEMORY_READABLE_BD_lemma",
  ``!READABLE.
    BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY clear_own TX_INVARIANT_MEMORY_READABLE_BD READABLE``,
  GEN_TAC THEN
  REWRITE_TAC [BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY_def] THEN
  REWRITE_TAC [BD_WRITE_clear_own_lemma] THEN
  REWRITE_TAC [BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_AP_PRESERVED_def] THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_BD_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [clear_own_PRESERVES_SOP_lemma, clear_own_PRESERVES_BP_lemma] THEN
  REWRITE_TAC [clear_own_PRESERVES_BO_lemma, clear_own_PRESERVES_BL_lemma]);

val TX_post_process_LAST_BD_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = store_thm (
  "TX_post_process_LAST_BD_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma",
  ``!nic nic' READABLE.
    LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_SET_EOQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (REWRITE_RULE [BD_AP_WRITE_PRESERVES_set_eoq_MEMORY_READABLE_BD_lemma] (SPECL [``set_eoq``, ``TX_INVARIANT_MEMORY_READABLE_BD``, ``tx_bd_queue nic``, ``nic.tx.current_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``, ``READABLE : 32 word -> bool``] BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_AP_QUEUE_PROPERTY_lemma)))) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM`` TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_INVARIANT_MEMORY_READABLE_DEPENDS_ONLY_ON_BD_AP_lemma] (SPECL [``TX_INVARIANT_MEMORY_READABLE_BD``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``, ``READABLE : 32 word -> bool``] BD_AP_QUEUE_BD_AP_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (GSYM (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_LAST_BD_PRESERVES_BD_QUEUE_lemma))) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = tx_bd_queue nic'`` ``EVERY (λbd_pa. TX_INVARIANT_MEMORY_READABLE_BD bd_pa nic'.regs.CPPI_RAM READABLE) (tx_bd_queue nic)`` THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_def]);

val TX_post_process_NOT_LAST_BD_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = store_thm (
  "TX_post_process_NOT_LAST_BD_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma",
  ``!nic nic' READABLE.
    ~LAST_BD nic.tx.current_bd /\
    TX_STATE_POST_PROCESS nic /\
    (nic' = tx_4post_process nic) /\
    TX_INVARIANT_WELL_DEFINED nic /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic)`` TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_STATE_POST_PROCESS_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_CLEAR_OWN_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [BD_AP_WRITE_PRESERVES_clear_own_MEMORY_READABLE_BD_lemma] (SPECL [``clear_own``, ``TX_INVARIANT_MEMORY_READABLE_BD``, ``tx_bd_queue nic``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``, ``READABLE : 32 word -> bool``] BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_AP_QUEUE_PROPERTY_lemma))) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM`` TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [TX_INVARIANT_MEMORY_READABLE_DEPENDS_ONLY_ON_BD_AP_lemma] (SPECL [``TX_INVARIANT_MEMORY_READABLE_BD``, ``tx_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``, ``READABLE : 32 word -> bool``] BD_AP_QUEUE_BD_AP_PROPERTY_PRESERVATION_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_post_process_NOT_LAST_BD_PRESERVES_BD_QUEUE_TAIL_lemma)) THEN
  ASM_RW_ASM_TAC ``tx_bd_queue nic = nic.tx.sop_bd_pa::tx_bd_queue nic'`` ``EVERY (λbd_pa. TX_INVARIANT_MEMORY_READABLE_BD bd_pa nic'.regs.CPPI_RAM READABLE) (tx_bd_queue nic)`` THEN
  RW_ASM_TAC ``EVERY (λbd_pa. TX_INVARIANT_MEMORY_READABLE_BD bd_pa nic'.regs.CPPI_RAM READABLE) (nic.tx.sop_bd_pa::tx_bd_queue nic')`` listTheory.EVERY_DEF THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_def]);

val tx_4post_process_PRESERVES_TX_SOP_BD_PA_lemma = store_thm (
  "tx_4post_process_PRESERVES_TX_SOP_BD_PA_lemma",
  ``!nic.
    LAST_BD nic.tx.current_bd
    ==>
    NIC_DELTA_PRESERVES_TX_SOP_BD_PA tx_4post_process nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def, tx_4post_process_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val tx_4post_process_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma = store_thm (
  "tx_4post_process_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma",
  ``!nic.
    ~LAST_BD nic.tx.current_bd
    ==>
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA tx_4post_process nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_def, tx_4post_process_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val tx_4post_process_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_lemma = store_thm (
  "tx_4post_process_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_lemma",
  ``!nic.
    NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA tx_4post_process nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_def] THEN
  Cases_on `LAST_BD nic.tx.current_bd` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL tx_4post_process_PRESERVES_TX_SOP_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL tx_4post_process_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val _ = export_theory();
