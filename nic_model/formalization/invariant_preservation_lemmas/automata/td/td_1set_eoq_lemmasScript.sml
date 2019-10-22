open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open tdInvariantTheory;
open bd_queue_preservation_lemmasTheory;
open tdTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open tx_state_definitionsTheory;
open td_invariant_preservation_definitionsTheory;
open tx_transition_definitionsTheory;
open it_transition_definitionsTheory;
open rx_transition_definitionsTheory;
open rd_transition_definitionsTheory;

val _ = new_theory "td_1set_eoq_lemmas";

val td_1set_eoq_cppi_ram_write_step_bd_pas_def = Define `
  td_1set_eoq_cppi_ram_write_step_bd_pas env nic =
  if env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic then
    [(set_eoq, nic.tx.current_bd_pa)]
  else if ~env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic then
    [(set_td, nic.tx.current_bd_pa)]
  else
    []`;

val td_1sets_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "td_1sets_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic
    ==>
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (td_1set_eoq env)
    nic
    (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [td_1set_eoq_def] THEN
  ASM_REWRITE_TAC [td_1set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val td_1sets_td_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "td_1sets_td_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    ~env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic
    ==>
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (td_1set_eoq env)
    nic
    (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [td_1set_eoq_def] THEN
  ASM_REWRITE_TAC [td_1set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  ASM_REWRITE_TAC [td_2set_td_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val td_1writes_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "td_1writes_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    ~TD_WRITE_CURRENT_BD_PA nic
    ==>
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (td_1set_eoq env)
    nic
    (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [td_1set_eoq_def] THEN
  ASM_REWRITE_TAC [td_1set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  ASM_REWRITE_TAC [td_2set_td_def] THEN
  ASM_REWRITE_TAC [td_3clear_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma]);

val td_1set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "td_1set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (td_1set_eoq env)
    nic
    (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  Cases_on `env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL td_1sets_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  Cases_on `~env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL td_1sets_td_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  Cases_on `~TD_WRITE_CURRENT_BD_PA nic` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL td_1writes_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  REPEAT (RW_ASM_TAC ``~P`` boolTheory.DE_MORGAN_THM) THEN
  REPEAT (KEEP_ASM_RW_ASM_TAC ``TD_WRITE_CURRENT_BD_PA nic`` ``P \/ Q``) THEN
  ASM_RW_ASM_TAC ``env.td.set_eoq`` ``~env.td.set_eoq`` THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val td_1set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "td_1set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)
    [nic.tx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [td_1set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_REFL_lemma, IN_EMPTY_LIST_IMP_IN_LIST_lemma] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_REFL_lemma, IN_EMPTY_LIST_IMP_IN_LIST_lemma]);

val td_1set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "td_1set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic env. PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [td_1set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] THEN
  REWRITE_TAC [set_eoq_lemmasTheory.set_eoq_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] THEN
  REWRITE_TAC [set_td_lemmasTheory.set_td_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]);

val td_1set_eoq_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "td_1set_eoq_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (td_1set_eoq env)
    nic
    (td_1set_eoq_cppi_ram_write_step_bd_pas env nic)
    [nic.tx.current_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [td_1set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [td_1set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [td_1set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);






val td_1set_eoq_REVERSE_PRESERVED_TX_STATE_IDLE_lemma = store_thm (
  "td_1set_eoq_REVERSE_PRESERVED_TX_STATE_IDLE_lemma",
  ``!nic env.
    TX_STATE_IDLE (td_1set_eoq env nic)
    ==>
    TX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_IDLE_def] THEN
  REWRITE_TAC [td_1set_eoq_def, td_2set_td_def, td_3clear_owner_and_hdp_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val td_1set_eoq_REVERSE_PRESERVED_TD_WRITE_CURRENT_BD_PA_lemma = store_thm (
  "td_1set_eoq_REVERSE_PRESERVED_TD_WRITE_CURRENT_BD_PA_lemma",
  ``!nic env.
    TD_WRITE_CURRENT_BD_PA (td_1set_eoq env nic)
    ==>
    TD_WRITE_CURRENT_BD_PA nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [td_1set_eoq_def, td_2set_td_def, td_3clear_owner_and_hdp_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val td_1set_eoq_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "td_1set_eoq_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma",
  ``!env. NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM (td_1set_eoq env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def] THEN
  GEN_TAC THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL td_1set_eoq_REVERSE_PRESERVED_TX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL td_1set_eoq_REVERSE_PRESERVED_TD_WRITE_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC []);












val td_1set_eoq_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma = store_thm (
  "td_1set_eoq_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma",
  ``!env.
    NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA (td_1set_eoq env)``,
  REWRITE_TAC [NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  REWRITE_TAC [td_1set_eoq_def, td_2set_td_def, td_3clear_owner_and_hdp_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);







val td_1set_eoq_PRESERVES_TX_STATE_IT_RX_RD_lemma = store_thm (
  "td_1set_eoq_PRESERVES_TX_STATE_IT_RX_RD_lemma",
  ``!env.
    NIC_DELTA_PRESERVES_TX_STATE (td_1set_eoq env) /\
    NIC_DELTA_PRESERVES_IT (td_1set_eoq env) /\
    NIC_DELTA_PRESERVES_RX (td_1set_eoq env) /\
    NIC_DELTA_PRESERVES_RD (td_1set_eoq env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_STATE_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_IT_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RD_def] THEN
  REWRITE_TAC [td_1set_eoq_def, td_2set_td_def, td_3clear_owner_and_hdp_def] THEN
  (let val t =
     GEN_TAC THEN
     COND_CASES_TAC THEN
     Cases_on `nic` THEN
     REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
     REWRITE_TAC [combinTheory.K_THM] THEN
     REWRITE_TAC [stateTheory.nic_state_accessors] THEN
     COND_CASES_TAC THEN
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

val td_1set_eoq_PRESERVES_DEAD_lemma = store_thm (
  "td_1set_eoq_PRESERVES_DEAD_lemma",
  ``!nic env nic'.
    (nic' = td_1set_eoq env nic)
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_1set_eoq_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  COND_CASES_TAC THENL
  [
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.nic_state_accessors]
   ,
   REWRITE_TAC [td_2set_td_def] THEN
   COND_CASES_TAC THENL
   [
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors]
    ,
    REWRITE_TAC [td_3clear_owner_and_hdp_def] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors]
   ]
  ]);

val td_1set_eoq_PRESERVES_RX_BUFFER_OFFSET_lemma = store_thm (
  "td_1set_eoq_PRESERVES_RX_BUFFER_OFFSET_lemma",
  ``!nic env nic'.
    (nic' = td_1set_eoq env nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_1set_eoq_def] THEN
  COND_CASES_TAC THENL
  [
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.nic_state_accessors] THEN
   Cases_on `n` THEN
   REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.nic_regs_accessors]
   ,
   REWRITE_TAC [td_2set_td_def] THEN
   COND_CASES_TAC THENL
   [
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `n` THEN
    REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_regs_accessors]
    ,
    REWRITE_TAC [td_3clear_owner_and_hdp_def] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `n` THEN
    REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_regs_accessors]
   ]
  ]);

val td_1set_eoq_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma = store_thm (
  "td_1set_eoq_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma",
  ``!nic env nic'.
    (nic' = td_1set_eoq env nic) /\
    ~TD_WRITE_CURRENT_BD_PA nic
    ==>
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_1set_eoq_def, td_2set_td_def, td_3clear_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val _ = export_theory();

