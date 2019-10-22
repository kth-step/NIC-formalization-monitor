open HolKernel Parse boolLib bossLib;
open helperTactics;
open txTheory;
open tx_state_definitionsTheory;
open tx_bd_queueTheory;
open tx_state_lemmasTheory;
open txInvariantWellDefinedTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open bd_listTheory;
open tx_invariant_well_defined_lemmasTheory;
open clear_own_lemmasTheory;
open tx_transition_definitionsTheory;

val _ = new_theory "tx_5clear_owner_and_hdp_lemmas";

val TX_clear_owner_and_hdp_NON_MODIFICATION_lemma = store_thm (
  "TX_clear_owner_and_hdp_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
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
  ASM_REWRITE_TAC [tx_5clear_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_WRITE_CP_lemma = store_thm (
  "tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_WRITE_CP_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    TX_STATE_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_5clear_owner_and_hdp_def, TX_STATE_WRITE_CP_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs_fupd, stateTheory.nic_state_tx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_regs, stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_state]);

val tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma = store_thm (
  "tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_clear_owner_and_hdp_CLEARS_CURRENT_BD_PA_SOP_BD_PA_NOT_EXPECTS_SOP_lemma = store_thm (
  "TX_clear_owner_and_hdp_CLEARS_CURRENT_BD_PA_SOP_BD_PA_NOT_EXPECTS_SOP_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    (nic'.tx.current_bd_pa = 0w) /\
    (nic'.tx.sop_bd_pa = 0w) /\
    ~nic'.tx.expects_sop``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_5clear_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_regs_fupd, stateTheory.nic_state_tx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_regs, stateTheory.nic_state_tx] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_current_bd_pa, stateTheory.tx_state_sop_bd_pa, stateTheory.tx_state_expects_sop]);

val TX_clear_owner_and_hdp_EMPTY_QUEUE_lemma = store_thm (
  "TX_clear_owner_and_hdp_EMPTY_QUEUE_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    BD_QUEUE [] nic'.tx.sop_bd_pa nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_CLEARS_CURRENT_BD_PA_SOP_BD_PA_NOT_EXPECTS_SOP_lemma)) THEN
  ASM_REWRITE_TAC [bd_queueTheory.BD_QUEUE_def]);

val TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma = store_thm (
  "TX_clear_owner_and_hdp_TX_BD_QUEUE_EQ_EMPTY_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    (tx_bd_queue nic' = [])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_EMPTY_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic' : nic_state``, ``[] : 32 word list``] TX_BD_QUEUE_IMP_tx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma = store_thm (
  "tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    ~TX_STATE_IDLE nic' /\
    ~TX_STATE_FETCH_NEXT_BD nic' /\
    ~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic' /\
    ~TX_STATE_PROCESS_MEMORY_READ_REPLY nic' /\
    ~TX_STATE_POST_PROCESS nic' /\
    ~TX_STATE_CLEAR_OWNER_AND_HDP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TX_STATE_WRITE_CP_DISTINCT_lemma THEN
  MATCH_MP_TAC tx_5clear_owner_and_hdp_IMP_NEXT_TX_STATE_WRITE_CP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

val TX_clear_owner_and_hdp_NOT_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_lemma = store_thm (
  "TX_clear_owner_and_hdp_NOT_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    ~TX_STATE_NOT_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_CLEARS_CURRENT_BD_PA_SOP_BD_PA_NOT_EXPECTS_SOP_lemma)) THEN
  ASM_REWRITE_TAC [TX_STATE_NOT_BD_QUEUE_EMPTY_def]);

val TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_EOP_STATE_lemma = store_thm (
  "TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_EOP_STATE_lemma",
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_EOP_STATE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_NOT_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_clear_owner_and_hdp_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma = store_thm (
  "TX_clear_owner_and_hdp_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma",
  ``!nic nic'.
    (nic' = tx_5clear_owner_and_hdp nic)
    ==>
    ~BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def, boolTheory.DE_MORGAN_THM] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_5clear_owner_and_hdp_NOT_NEXT_TX_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma = store_thm (
  "TX_clear_owner_and_hdp_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma",
  ``!nic nic'.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    (nic' = tx_5clear_owner_and_hdp nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_clear_owner_and_hdp_NOT_BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma)) THEN
  ASM_REWRITE_TAC []);

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas_def = Define `
  tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic = [(clear_own, nic.tx.sop_bd_pa)]`;

val tx_5clear_owner_and_hdp_WRITES_CPPI_RAM_lemma = store_thm (
  "tx_5clear_owner_and_hdp_WRITES_CPPI_RAM_lemma",
  ``!nic.
    ((tx_5clear_owner_and_hdp nic).regs.CPPI_RAM =
     cppi_ram_write nic.regs.CPPI_RAM (tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic))``,
  GEN_TAC THEN
  REWRITE_TAC [tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  ASM_REWRITE_TAC [tx_5clear_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val tx_5clear_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "tx_5clear_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
      tx_5clear_owner_and_hdp
      nic
      (tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  REWRITE_TAC [tx_5clear_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val tx_5clear_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma = store_thm (
  "tx_5clear_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    (tx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  ASM_REWRITE_TAC [tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC TX_NOT_BD_QUEUE_EMPTY_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_CLEAR_OWNER_AND_HDP_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_5clear_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "tx_5clear_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
      (tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [listTheory.MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]);

val tx_5clear_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "tx_5clear_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      tx_5clear_owner_and_hdp
      nic
      (tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
      (tx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_5clear_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_5clear_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [tx_5clear_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val tx_5clear_owner_and_hdp_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_5clear_owner_and_hdp_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic q.
    TX_STATE_CLEAR_OWNER_AND_HDP nic /\
    TX_INVARIANT_BD_QUEUE_FINITE nic /\
    TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM (tx_5clear_owner_and_hdp nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ``tx_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic : cppi_ram_write_step_bd_pas_type`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_5clear_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val tx_5clear_owner_and_hdp_CLEARS_TX_SOP_BD_PA_lemma = store_thm (
  "tx_5clear_owner_and_hdp_CLEARS_TX_SOP_BD_PA_lemma",
  ``!nic. NIC_DELTA_CLEARS_TX_SOP_BD_PA tx_5clear_owner_and_hdp nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CLEARS_TX_SOP_BD_PA_def, tx_5clear_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val _ = export_theory();
