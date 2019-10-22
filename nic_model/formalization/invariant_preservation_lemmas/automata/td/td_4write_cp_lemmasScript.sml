open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open tdTheory;
open bd_listTheory;
open tx_state_definitionsTheory;
open td_invariant_preservation_definitionsTheory;
open tdInvariantTheory;
open tx_transition_definitionsTheory;
open it_transition_definitionsTheory;
open rx_transition_definitionsTheory;
open rd_transition_definitionsTheory;

val _ = new_theory "td_4write_cp_lemmas";

val td_4write_cp_cppi_ram_write_step_bd_pas_def = Define `
  td_4write_cp_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val td_4write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "td_4write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (td_4write_cp env)
    nic
    td_4write_cp_cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [td_4write_cp_def] THEN
  REWRITE_TAC [td_4write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val td_4write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "td_4write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic. CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE td_4write_cp_cppi_ram_write_step_bd_pas [nic.tx.current_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [td_4write_cp_cppi_ram_write_step_bd_pas_def, listTheory.MAP] THEN
  REWRITE_TAC [IN_EMPTY_LIST_IMP_IN_LIST_lemma]);

val td_4write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "td_4write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION td_4write_cp_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [td_4write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF]);

val td_4write_cp_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "td_4write_cp_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (td_4write_cp env)
    nic
    td_4write_cp_cppi_ram_write_step_bd_pas
    [nic.tx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [td_4write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [td_4write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [td_4write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);





val td_4write_cp_REVERSE_PRESERVED_TX_STATE_IDLE_lemma = store_thm (
  "td_4write_cp_REVERSE_PRESERVED_TX_STATE_IDLE_lemma",
  ``!nic env.
    TX_STATE_IDLE (td_4write_cp env nic)
    ==>
    TX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_IDLE_def] THEN
  REWRITE_TAC [td_4write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val td_4write_cp_REVERSE_PRESERVED_TD_WRITE_CURRENT_BD_PA_lemma = store_thm (
  "td_4write_cp_REVERSE_PRESERVED_TD_WRITE_CURRENT_BD_PA_lemma",
  ``!nic env.
    TD_WRITE_CURRENT_BD_PA (td_4write_cp env nic)
    ==>
    TD_WRITE_CURRENT_BD_PA nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [td_4write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val td_4write_cp_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "td_4write_cp_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma",
  ``!env. NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM (td_4write_cp env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def] THEN
  GEN_TAC THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL td_4write_cp_REVERSE_PRESERVED_TX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL td_4write_cp_REVERSE_PRESERVED_TD_WRITE_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC []);






val td_4write_cp_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma = store_thm (
  "td_4write_cp_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma",
  ``!env.
    NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA (td_4write_cp env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  REWRITE_TAC [td_4write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);




val td_4write_cp_PRESERVES_TX_STATE_IT_RX_RD_lemma = store_thm (
  "td_4write_cp_PRESERVES_TX_STATE_IT_RX_RD_lemma",
  ``!env.
    NIC_DELTA_PRESERVES_TX_STATE (td_4write_cp env) /\
    NIC_DELTA_PRESERVES_IT (td_4write_cp env) /\
    NIC_DELTA_PRESERVES_RX (td_4write_cp env) /\
    NIC_DELTA_PRESERVES_RD (td_4write_cp env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_STATE_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_IT_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RD_def] THEN
  REWRITE_TAC [td_4write_cp_def] THEN
  (let val t =
     GEN_TAC THEN
     Cases_on `nic` THEN
     REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
     REWRITE_TAC [combinTheory.K_THM] THEN
     REWRITE_TAC [stateTheory.nic_state_accessors] THEN
     Cases_on `t` THEN
     REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
     REWRITE_TAC [combinTheory.K_THM] THEN
     REWRITE_TAC [stateTheory.tx_state_accessors]
   in
   CONJ_TAC THENL
   [
    t
    ,
    CONJ_TAC THENL
    [
     t
     ,
     CONJ_TAC THEN
     t
    ]
   ]
   end));

val td_4write_cp_PRESERVES_DEAD_lemma = store_thm (
  "td_4write_cp_PRESERVES_DEAD_lemma",
  ``!nic env nic'.
    (nic' = td_4write_cp env nic)
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_4write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors]);

val td_4write_cp_PRESERVES_RX_BUFFER_OFFSET_lemma = store_thm (
  "td_4write_cp_PRESERVES_RX_BUFFER_OFFSET_lemma",
  ``!nic env nic'.
    (nic' = td_4write_cp env nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_4write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val td_4write_cp_PRESERVES_CPPI_RAM_lemma = store_thm (
  "td_4write_cp_PRESERVES_CPPI_RAM_lemma",
  ``!nic env nic'.
    (nic' = td_4write_cp env nic)
    ==>
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_4write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val _ = export_theory();

