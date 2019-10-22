open HolKernel Parse boolLib bossLib;
open helperTactics;
open nic_rw_tactics;
open rdTheory;
open bd_queue_preservation_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open rdInvariantTheory;
open rd_state_definitionsTheory;
open rx_transition_definitionsTheory;
open rx_state_definitionsTheory;

val _ = new_theory "rd_3set_eoq_lemmas";

val nic_with_rw_tactic =
  rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors];

val regs_with_rw_tactic =
  rw_state_tactic
  `n`
  [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors];

val rd_3set_eoq_cppi_ram_write_step_bd_pas_case_def = Define `
  (rd_3set_eoq_cppi_ram_write_step_bd_pas_case T T nic = [(set_eoq, nic.rx.current_bd_pa)]) /\
  (rd_3set_eoq_cppi_ram_write_step_bd_pas_case T F nic = [(set_td, nic.rx.current_bd_pa)]) /\
  (rd_3set_eoq_cppi_ram_write_step_bd_pas_case F _ nic = [])`;

val rd_3set_eoq_cppi_ram_write_step_bd_pas_def = Define `
  rd_3set_eoq_cppi_ram_write_step_bd_pas env nic =
  rd_3set_eoq_cppi_ram_write_step_bd_pas_case
  (RD_WRITE_CURRENT_BD_PA nic)
  env.rd.set_eoq
  nic`;

val rd_3set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rd_3set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rd_3set_eoq env)
    nic
    (rd_3set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [rd_3set_eoq_def, rd_4set_td_def, rd_5clear_owner_and_hdp_def] THEN
  ASM_CASES_TAC ``RD_WRITE_CURRENT_BD_PA nic`` THEN
  ASM_CASES_TAC ``env.rd.set_eoq`` THEN
  ASM_REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_case_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  nic_with_rw_tactic THEN
  regs_with_rw_tactic);

val rd_3set_eoq_cppi_ram_write_step_bd_pas_IN_RX_CURRENT_BD_PA_lemma = store_thm (
  "rd_3set_eoq_cppi_ram_write_step_bd_pas_IN_RX_CURRENT_BD_PA_lemma",
  ``!nic env.
    IN_LIST1_IMP_IN_LIST2
    (MAP SND (rd_3set_eoq_cppi_ram_write_step_bd_pas env nic))
    [nic.rx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  ASM_CASES_TAC ``RD_WRITE_CURRENT_BD_PA nic`` THEN
  ASM_CASES_TAC ``env.rd.set_eoq`` THEN
  ASM_REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_case_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma] THEN
  REWRITE_TAC [IN_EMPTY_LIST_IMP_IN_LIST_lemma]);

val rd_3set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_3set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (rd_3set_eoq_cppi_ram_write_step_bd_pas env nic)
    [nic.rx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_IN_RX_CURRENT_BD_PA_lemma]);

val CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemmas = [
  set_eoq_lemmasTheory.set_eoq_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma,
  set_td_lemmasTheory.set_td_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma];

val rd_3set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rd_3set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic env.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION (rd_3set_eoq_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_def] THEN
  ASM_CASES_TAC ``RD_WRITE_CURRENT_BD_PA nic`` THEN
  ASM_CASES_TAC ``env.rd.set_eoq`` THEN
  ASM_REWRITE_TAC [rd_3set_eoq_cppi_ram_write_step_bd_pas_case_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  REWRITE_TAC CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemmas);

val rd_3set_eoq_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_3set_eoq_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rd_3set_eoq env)
    nic
    (rd_3set_eoq_cppi_ram_write_step_bd_pas env nic)
    [nic.rx.current_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rd_3set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rd_3set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rd_3set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);



val nic_r0_with_rw_tactic =
  nic_with_rw_tactic THEN
  rw_state_tactic
  `r0`
  [stateTheory.rd_state_fn_updates, combinTheory.K_THM, stateTheory.rd_state_accessors] THEN
  REWRITE_TAC [stateTheory.rd_abstract_state_distinct];

val rd_3set_eoq_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "rd_3set_eoq_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic env nic'.
    (nic' = rd_3set_eoq env nic)
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_3set_eoq_def, rd_4set_td_def] THEN
  REWRITE_TAC [rd_5clear_owner_and_hdp_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  REWRITE_TAC [boolTheory.IMP_DISJ_THM] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  REPEAT (
  COND_CASES_TAC THENL
  [
   nic_r0_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  nic_with_rw_tactic THEN
  rw_state_tactic `r` [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_with_rw_tactic =
  rw_state_tactic
  `r`
  [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors];

val rd_3set_eoq_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma = store_thm (
  "rd_3set_eoq_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma",
  ``!nic env nic'.
    (nic' = rd_3set_eoq env nic) /\
    RD_ENABLE nic
    ==>
    ~RD_STATE_WRITE_CP nic' \/
   ((nic'.rx.sop_bd_pa = 0w) /\ RX_STATE_IDLE nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.RD_ENABLE_def, RD_STATE_WRITE_CP_def, RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  SPLIT_ASM_TAC THEN
  WEAKEN_TAC (fn term => is_neg term) THEN
  WEAKEN_TAC (fn term => (is_comb o #2 o dest_eq) term) THEN
  REWRITE_TAC [rd_3set_eoq_def, rd_4set_td_def] THEN
  REWRITE_TAC [rd_5clear_owner_and_hdp_def] THEN
  REPEAT (
  COND_CASES_TAC THENL
  [
   nic_r0_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic THEN
  RW_ASM_TAC ``x = y`` stateTheory.nic_state_rx THEN
  RW_ASM_TAC ``x = y`` stateTheory.rx_state_state THEN
  ASM_REWRITE_TAC []);

val rd_3set_eoq_IMP_NOT_NEXT_RD_STATE_IDLE_lemma = store_thm (
  "rd_3set_eoq_IMP_NOT_NEXT_RD_STATE_IDLE_lemma",
  ``!nic env nic'.
    (nic' = rd_3set_eoq env nic)
    ==>
    ~RD_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.RD_ENABLE_def, RD_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rd_3set_eoq_def, rd_4set_td_def] THEN
  REWRITE_TAC [rd_5clear_owner_and_hdp_def] THEN
  REPEAT (
  COND_CASES_TAC THENL
  [
   nic_r0_with_rw_tactic THEN
   REWRITE_TAC [GSYM stateTheory.rd_abstract_state_distinct]
   ,
   ALL_TAC
  ]) THEN
  nic_r0_with_rw_tactic THEN
  REWRITE_TAC [GSYM stateTheory.rd_abstract_state_distinct]);

val _ = export_theory();

