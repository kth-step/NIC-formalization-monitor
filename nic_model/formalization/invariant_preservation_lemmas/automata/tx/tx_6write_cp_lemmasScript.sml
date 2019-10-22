open HolKernel Parse boolLib bossLib;
open helperTactics;
open txTheory;
open tx_transition_definitionsTheory;
open bd_queue_preservation_lemmasTheory;
open tx_bd_queueTheory;
open tx_state_definitionsTheory;
open tx_state_lemmasTheory;


open txInvariantWellDefinedTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open tx_invariant_well_defined_lemmasTheory;
open clear_own_lemmasTheory;

val _ = new_theory "tx_6write_cp_lemmas";

val TX_write_cp_NON_MODIFICATION_lemma = store_thm (
  "TX_write_cp_NON_MODIFICATION_lemma",
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.tx.current_bd_pa = nic.tx.current_bd_pa) /\
    (nic'.tx.sop_bd_pa = nic.tx.sop_bd_pa) /\
    (nic'.tx.expects_sop = nic.tx.expects_sop) /\
    (nic'.tx.current_bd.eop = nic.tx.current_bd.eop) /\
    (nic'.tx.current_bd.ndp = nic.tx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_6write_cp_def] THEN
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

val tx_6write_cp_PRESERVES_TX_SOP_BD_PA_lemma = store_thm (
  "tx_6write_cp_PRESERVES_TX_SOP_BD_PA_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_TX_SOP_BD_PA (tx_6write_cp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``tx_6write_cp env nic``] TX_write_cp_NON_MODIFICATION_lemma)]);

val tx_6write_cp_PRESERVES_CPPI_RAM_lemma = store_thm (
  "tx_6write_cp_PRESERVES_CPPI_RAM_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_CPPI_RAM (tx_6write_cp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``tx_6write_cp env nic``] TX_write_cp_NON_MODIFICATION_lemma)]);

val TX_write_cp_PRESERVES_QUEUE_lemma = store_thm (
  "TX_write_cp_PRESERVES_QUEUE_lemma",
  ``!nic env nic'.
    TX_STATE_WRITE_CP nic /\
    (nic' = tx_6write_cp env nic)
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_SOP_BD_PA_AND_CPPI_RAM_AND_TX_INVARIANT_BD_QUEUE_FINITE_IMP_EQ_BD_QUEUES_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_write_cp_NEXT_STATE_EQ_idle_OR_fetch_next_bd_lemma = prove (
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    TX_STATE_IDLE nic' \/ TX_STATE_FETCH_NEXT_BD nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_6write_cp_def, TX_STATE_IDLE_def, TX_STATE_FETCH_NEXT_BD_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC []);

val tx_6write_cp_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma = store_thm (
  "tx_6write_cp_IMP_NEXT_TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_lemma",
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_NEXT_STATE_EQ_idle_OR_fetch_next_bd_lemma)) THEN
  ASM_REWRITE_TAC [boolTheory.DISJ_ASSOC]);

val TX_write_cp_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_IMP_NEXT_STATE_EQ_fetch_next_bd_lemma = store_thm (
  "TX_write_cp_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_IMP_NEXT_STATE_EQ_fetch_next_bd_lemma",
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic) /\
    TX_STATE_NOT_BD_QUEUE_EMPTY nic'
    ==>
    TX_STATE_FETCH_NEXT_BD nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_NOT_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (IMP_TRANS (SPEC_ALL TX_write_cp_NEXT_STATE_EQ_idle_OR_fetch_next_bd_lemma) (SPEC ``nic' : nic_state`` TX_STATE_EQ_idle_OR_fetch_next_bd_NEQ_lemma))) THEN
  ASM_RW_ASM_TAC ``P /\ Q`` ``P \/ Q`` THEN
  ASM_REWRITE_TAC []);

val TX_write_cp_NEXT_STATE_EQ_fetch_next_bd_IMP_current_bd_pa_NEQ_ZERO_lemma = prove (
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic) /\
    TX_STATE_FETCH_NEXT_BD nic'
    ==>
    nic.tx.current_bd_pa <> 0w``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_FETCH_NEXT_BD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``nic' = tx_6write_cp env nic`` ``nic'.tx.state = tx_fetch_next_bd`` THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  REWRITE_TAC [tx_6write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  COND_CASES_TAC THEN
  RW_ASM_TAC ``P`` boolTheory.DE_MORGAN_THM THEN
  ASM_REWRITE_TAC [stateTheory.tx_abstract_state_distinct]);

val TX_write_cp_CURRENT_BD_PA_EQ_SOP_BD_PA_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "TX_write_cp_CURRENT_BD_PA_EQ_SOP_BD_PA_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic env nic'.
    TX_STATE_WRITE_CP nic /\
    (nic' = tx_6write_cp env nic) /\
    TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    TX_STATE_NOT_BD_QUEUE_EMPTY nic'
    ==>
    TX_STATE_NOT_BD_QUEUE_EMPTY nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_IMP_NEXT_STATE_EQ_fetch_next_bd_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_NEXT_STATE_EQ_fetch_next_bd_IMP_current_bd_pa_NEQ_ZERO_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic`` TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def THEN
  ASM_RW_ASM_TAC ``nic.tx.current_bd_pa = nic.tx.sop_bd_pa`` ``nic.tx.current_bd_pa <> 0w`` THEN
  ASM_REWRITE_TAC [TX_STATE_NOT_BD_QUEUE_EMPTY_def]);

val TX_write_cp_PRESERVES_CURRENT_BD_EOP_STATE_lemma = store_thm (
  "TX_write_cp_PRESERVES_CURRENT_BD_EOP_STATE_lemma",
  ``!nic env nic'.
    TX_STATE_WRITE_CP nic /\
    (nic' = tx_6write_cp env nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_EOP_STATE_def] THEN
  DISCH_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_CURRENT_BD_PA_EQ_SOP_BD_PA_TX_STATE_NOT_BD_QUEUE_EMPTY_NEXT_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_STATE nic`` TX_INVARIANT_CURRENT_BD_STATE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_EOP_STATE nic`` TX_INVARIANT_CURRENT_BD_EOP_STATE_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH_ALL (SPEC_ALL TX_write_cp_NON_MODIFICATION_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_write_cp_IMP_NOT_BD_QUEUE_ADVANCEMENET_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma = store_thm (
  "TX_write_cp_IMP_NOT_BD_QUEUE_ADVANCEMENET_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma",
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    ~BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (IMP_TRANS (SPEC_ALL TX_write_cp_NEXT_STATE_EQ_idle_OR_fetch_next_bd_lemma) (SPEC ``nic' : nic_state`` TX_STATE_EQ_idle_OR_fetch_next_bd_NEQ_lemma))) THEN
  ASM_REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def]);

val TX_write_cp_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma = store_thm (
  "TX_write_cp_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma",
  ``!nic env nic'.
    TX_STATE_WRITE_CP nic /\
    (nic' = tx_6write_cp env nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_write_cp_IMP_NOT_BD_QUEUE_ADVANCEMENET_DEPENDS_ON_NONZERO_NDP_STATE_NEXT_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_write_cp_NEXT_STATE_NEQ_lemma = store_thm (
  "TX_write_cp_NEXT_STATE_NEQ_lemma",
  ``!nic env nic'.
    (nic' = tx_6write_cp env nic)
    ==>
    ~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic' /\
    ~TX_STATE_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_write_cp_NEXT_STATE_EQ_idle_OR_fetch_next_bd_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` TX_STATE_EQ_idle_OR_fetch_next_bd_NEQ_lemma)) THEN
  ASM_REWRITE_TAC []);

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val tx_6write_cp_cppi_ram_write_step_bd_pas_def = Define `
  tx_6write_cp_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val tx_6write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "tx_6write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
      (tx_6write_cp env)
      nic
      tx_6write_cp_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [tx_6write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``tx_6write_cp env nic``] TX_write_cp_NON_MODIFICATION_lemma)]);

val tx_6write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma = store_thm (
  "tx_6write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    tx_6write_cp_cppi_ram_write_step_bd_pas
    (tx_bd_queue nic)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_6write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val tx_6write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "tx_6write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
      tx_6write_cp_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [tx_6write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [listTheory.MEM]);

val tx_6write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "tx_6write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      (tx_6write_cp env)
      nic
      tx_6write_cp_cppi_ram_write_step_bd_pas
      (tx_bd_queue nic)``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_6write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [tx_6write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [tx_6write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val tx_6write_cp_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_6write_cp_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic env q.
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM (tx_6write_cp env nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ``tx_6write_cp_cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [tx_6write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val _ = export_theory();
