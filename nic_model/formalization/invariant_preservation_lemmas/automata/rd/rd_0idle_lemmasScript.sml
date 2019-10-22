open HolKernel Parse boolLib bossLib;
open helperTactics;
open nic_rw_tactics;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open rdTheory;
open bd_listTheory;
open rd_state_definitionsTheory;
open rd_state_lemmasTheory;
open rdInvariantTheory;

val _ = new_theory "rd_0idle_lemmas";

val rd_0idle_cppi_ram_write_step_bd_pas_def = Define `
  rd_0idle_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val rd_0idle_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rd_0idle_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    rd_0idle
    nic
    rd_0idle_cppi_ram_write_step_bd_pas``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [rd_0idle_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [rd_0idle_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors]);

val rd_0idle_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_0idle_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rd_0idle_cppi_ram_write_step_bd_pas
    [nic.rx.current_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rd_0idle_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_EMPTY_LIST_IMP_IN_LIST_lemma]);

val rd_0idle_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rd_0idle_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION rd_0idle_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [rd_0idle_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val rd_0idle_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_0idle_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    rd_0idle
    nic
    rd_0idle_cppi_ram_write_step_bd_pas
    [nic.rx.current_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rd_0idle_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rd_0idle_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rd_0idle_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);



val rd_0idle_PRESERVES_NOT_RX_STATE_WRITE_CP_lemma = store_thm (
  "rd_0idle_PRESERVES_NOT_RX_STATE_WRITE_CP_lemma",
  ``!nic nic'.
    (nic' = rd_0idle nic) /\
    ~RD_STATE_WRITE_CP nic
    ==>
    ~RD_STATE_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_0idle_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic `nic'` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_11] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC []);

val rd_0idle_RD_STATE_IDLE_IMP_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "rd_0idle_RD_STATE_IDLE_IMP_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic nic'.
    (nic' = rd_0idle nic) /\
    RD_STATE_IDLE nic
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_STATE_IDLE_IMP_NOT_RD_STATE_WRITE_CP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_0idle_PRESERVES_NOT_RX_STATE_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC []);


val rd_0idle_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma = store_thm (
  "rd_0idle_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma",
  ``!nic nic'.
    (nic' = rd_0idle nic) /\
    RD_STATE_IDLE nic
    ==>
    ~RD_STATE_WRITE_CP nic' \/
   ((nic'.rx.sop_bd_pa = 0w) /\ RX_STATE_IDLE nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_STATE_IDLE_IMP_NOT_RD_STATE_WRITE_CP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_0idle_PRESERVES_NOT_RX_STATE_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

