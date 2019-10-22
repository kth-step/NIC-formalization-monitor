open HolKernel Parse boolLib bossLib;
open nic_rw_tactics;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open rdTheory;
open bd_listTheory;
open rdInvariantTheory;
open rd_state_definitionsTheory;

val _ = new_theory "rd_6write_cp_lemmas";

val rd_6write_cp_cppi_ram_write_step_bd_pas_def = Define `
  rd_6write_cp_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val rd_6write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rd_6write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rd_6write_cp env)
    nic
    rd_6write_cp_cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [rd_6write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic `n` [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors]);

val rd_6write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_6write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rd_6write_cp_cppi_ram_write_step_bd_pas
    [nic.rx.current_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rd_6write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_EMPTY_LIST_IMP_IN_LIST_lemma]);

val rd_6write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rd_6write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION rd_6write_cp_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [rd_6write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val rd_6write_cp_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_6write_cp_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rd_6write_cp env)
    nic
    rd_6write_cp_cppi_ram_write_step_bd_pas
    [nic.rx.current_bd_pa]``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rd_6write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rd_6write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rd_6write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);



val rd_6write_cp_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "rd_6write_cp_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic env nic'.
    (nic' = rd_6write_cp env nic)
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic `r0` [stateTheory.rd_state_fn_updates, combinTheory.K_THM, stateTheory.rd_state_accessors] THEN
  REWRITE_TAC [stateTheory.rd_abstract_state_distinct]);



val rd_6write_cp_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma = store_thm (
  "rd_6write_cp_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma",
  ``!nic env nic'.
    (nic' = rd_6write_cp env nic) /\
    RD_ENABLE nic
    ==>
    ~RD_STATE_WRITE_CP nic' \/
   ((nic'.rx.sop_bd_pa = 0w) /\ RX_STATE_IDLE nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic
  `r0`
  [stateTheory.rd_state_fn_updates, combinTheory.K_THM, stateTheory.rd_state_accessors] THEN
  REWRITE_TAC [stateTheory.rd_abstract_state_distinct]);

val rd_6write_cp_NOT_MODIFIED_lemma = store_thm (
  "rd_6write_cp_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rd_6write_cp env nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rd_6write_cp_def] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic `r` [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val _ = export_theory();

