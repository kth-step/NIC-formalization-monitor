open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open set_rx_overrun_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_lemmasTheory;
open rx_18clear_sop_owner_and_hdp_lemmasTheory;
open rx_bd_queueTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open rx_state_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedLemmasTheory;
open bd_listTheory;
open rx_state_definitionsTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT1_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT2_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemmasTheory;

val _ = new_theory "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_lemmas";

(********************************************************************)
(*Lemmas for all four cases of overrun (sop, eop, both, no overrun).*)
(********************************************************************)

val rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def, LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_17clear_sop_owner_and_hdp_NOT_MODIFIED_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);
  
val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_MODIFIED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_NOT_MODIFIED_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_EQ_BETA_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_EQ_BETA_lemma",
  ``!nic env.
    rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic =
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC []);

(***************************************************************************)
(*End of lemmas for all four cases of overrun (sop, eop, both, no overrun).*)
(***************************************************************************)













(***********************************************************************)
(*Lemmas concerning setting the overrun bit in the SOP/EOP/SOP and EOP.*)
(***********************************************************************)

val rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    nic.rx.overrun /\
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def, LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_NOT_MODIFIED_EQ_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NOT_MODIFIED_EQ_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    ((rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic).rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  ASM_REWRITE_TAC [stateTheory.overrun_case_case_def, LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NOT_MODIFIED_EQ_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def = Define `
  rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic =
  case env.rx.sop_eop_both_overrun of
    | sop_overrun => [(set_rx_overrun, nic.rx.sop_bd_pa)]
    | eop_overrun => [(set_rx_overrun, nic.rx.eop_bd_pa)]
    | sop_eop_both =>  [(set_rx_overrun, nic.rx.sop_bd_pa); (set_rx_overrun, nic.rx.eop_bd_pa)]`;

val MEM_rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "MEM_rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_lemma",
  ``!bd_pa env nic.
    MEM bd_pa (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic))
    ==>
    (bd_pa = nic.rx.sop_bd_pa) \/ (bd_pa = nic.rx.eop_bd_pa)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
   Cases_on `env.rx.sop_eop_both_overrun` THEN
   REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
   REWRITE_TAC [listTheory.MAP, listTheory.MEM, boolTheory.OR_INTRO_THM1, boolTheory.OR_INTRO_THM2]);

val rx_17set_sop_eop_overrun_WRITES_CPPI_RAM_lemma = store_thm (
  "rx_17set_sop_eop_overrun_WRITES_CPPI_RAM_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    ((rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic).regs.CPPI_RAM =
     cppi_ram_write nic.regs.CPPI_RAM (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  REWRITE_TAC [cppi_ram_write_TWO_STEPS_EQ_cppi_ram_write_TWO_STEPS_lemma] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_17set_sop_overrun_CPPI_RAM_EQ_lemma = store_thm (
  "rx_17set_sop_overrun_CPPI_RAM_EQ_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = sop_overrun)
    ==>
    (cppi_ram_write nic.regs.CPPI_RAM (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
     =
     set_rx_overrun nic.regs.CPPI_RAM nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val rx_17set_eop_overrun_CPPI_RAM_EQ_lemma = store_thm (
  "rx_17set_eop_overrun_CPPI_RAM_EQ_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = eop_overrun)
    ==>
    (cppi_ram_write nic.regs.CPPI_RAM (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
     =
     set_rx_overrun nic.regs.CPPI_RAM nic.rx.eop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val rx_17set_both_overrun_CPPI_RAM_EQ_lemma = store_thm (
  "rx_17set_both_overrun_CPPI_RAM_EQ_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = both_overrun)
    ==>
    (cppi_ram_write nic.regs.CPPI_RAM (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
     =
     set_rx_overrun (set_rx_overrun nic.regs.CPPI_RAM nic.rx.sop_bd_pa) nic.rx.eop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [cppi_ram_write_TWO_STEPS_EQ_cppi_ram_write_TWO_STEPS_lemma]);

val rx_17set_sop_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma = store_thm (
  "rx_17set_sop_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = sop_overrun)
    ==>
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic) = [nic.rx.sop_bd_pa])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_17set_eop_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma = store_thm (
  "rx_17set_eop_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = eop_overrun)
    ==>
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic) = [nic.rx.eop_bd_pa])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_17set_both_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma = store_thm (
  "rx_17set_both_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = both_overrun)
    ==>
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic) = [nic.rx.sop_bd_pa; nic.rx.eop_bd_pa])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_17set_sop_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma = store_thm (
  "rx_17set_sop_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = sop_overrun)
    ==>
    (MAP FST (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic) = [set_rx_overrun])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_17set_eop_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma = store_thm (
  "rx_17set_eop_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = eop_overrun)
    ==>
    (MAP FST (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic) = [set_rx_overrun])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_17set_both_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma = store_thm (
  "rx_17set_both_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma",
  ``!nic env.
    (env.rx.sop_eop_both_overrun = both_overrun)
    ==>
    (MAP FST (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic) = [set_rx_overrun; set_rx_overrun])``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
    (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_AND_BD_STRUCTURE_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma)) THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  Cases_on `env.rx.sop_eop_both_overrun` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_eop_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_both_overrun_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC MEM2_LIST1_IMP_IN_LIST2_lemma THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17set_sop_eop_overrun_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_17set_sop_eop_overrun_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic env.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  Cases_on `env.rx.sop_eop_both_overrun` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [listTheory.EVERY_DEF] THEN
   REWRITE_TAC [set_rx_overrun_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_eop_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [listTheory.EVERY_DEF] THEN
   REWRITE_TAC [set_rx_overrun_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_both_overrun_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [listTheory.EVERY_DEF] THEN
   REWRITE_TAC [set_rx_overrun_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]
  ]);

val rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
    (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_17set_sop_eop_overrun_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic env.
    nic.rx.overrun /\
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ONCE_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_EQ_BETA_lemma] THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    nic.rx.overrun /\
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_NOT_MODIFIED_EQ_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NOT_MODIFIED_EQ_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    ((rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic).rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic``] rx_17set_sop_eop_overrun_NOT_MODIFIED_lemma)]);

val rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  COPY_ASM_TAC ``BD_QUEUE q a m`` THEN
  RW_ASM_TAC ``BD_QUEUE q a m`` (GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma)  THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_BD_QUEUE_lemma)))) THEN
  REFLECT_ASM_TAC ``r = f a1 a2`` THEN
  KEEP_ASM_RW_ASM_TAC ``f a1 a2 = r`` ``BD_QUEUE q a (f a1 a2).regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NOT_MODIFIED_EQ_lemma)) THEN
  ASM_RW_ASM_TAC ``f a1 a2 = r`` ``(f a1 a2).rx.sop_bd_pa = nic.rx.sop_bd_pa`` THEN
  REFLECT_ASM_TAC ``nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa`` THEN
  ASM_RW_ASM_TAC ``nic.rx.sop_bd_pa = nic'.rx.sop_bd_pa`` ``BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic'.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic' : nic_state``, ``rx_bd_queue nic``] RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

(******************************************************************************)
(*End of lemmas concerning setting the overrun bit in the SOP/EOP/SOP and EOP.*)
(******************************************************************************)

(*******************************)
(*Lemmas concerning no overrun.*)
(*******************************)

val rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma",
  ``!nic env.
    ~nic.rx.overrun
    ==>
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic =
     rx_18clear_sop_owner_and_hdp nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def]);

(**************************************)
(*End of lemmas concerning no overrun.*)
(**************************************)

























(******Start of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE when there is overrun********)

val rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_lemma = store_thm (
  "rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_def, listTheory.MEM, boolTheory.OR_INTRO_THM2] THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_def, listTheory.MEM, boolTheory.OR_INTRO_THM1] THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_def, listTheory.MEM, DECIDE ``P \/ Q ==> Q \/ P``]);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_lemma",
  ``!nic env.
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic
    ==>
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA
    nic
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_def]);

val RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma = store_thm (
  "RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma",
  ``!nic env.
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic
    ==>
    RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA
    nic
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_def]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_17set_sop_eop_overrun_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma",
  ``!nic env.
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  COND_CASES_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_NEXT_RX_STATE_rx_clear_sop_owner_and_hdp_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NEXT_RX_STATE_rx_clear_sop_owner_and_hdp_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    ((rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic).rx.state = rx_clear_sop_owner_and_hdp)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_state]);

val rx_17set_sop_eop_overrun_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma = store_thm (
  "rx_17set_sop_eop_overrun_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NEXT_RX_STATE_rx_clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_EQ_BETA_lemma] THEN
  MATCH_MP_TAC NIC_DELTA_BETWEEN_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_PRESERVES_BD_QUEUE_LOCATION_IMP_BD_QUEUE_STRUCTURE_PRESERVED_lemma THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_CURRENT_BD_PA_lemma)) THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC []);

(******End of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE when there is overrun********)

(******Start of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE when there is no overrun********)

val rx_17clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_RW_ASM_TAC ``f a1 a2 = g a`` ``v = f a1 s2`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma)) THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_def] THEN
  EXISTS_TAC ``[] : bd_pa_type list`` THEN
  REWRITE_TAC [listTheory.APPEND] THEN
  MATCH_MP_TAC (GSYM RX_write_cp_IMP_unseen_bd_queue_EQ_bd_queue_lemma) THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_NEXT_STATE_RX_STATE_WRITE_CP_lemma]);

(******End of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE when there is no overrun********)




(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_CPPI_RAM_AND_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT1_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

val rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_NEXT_STATE_WRITE_CP_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_NEXT_STATE_WRITE_CP_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun
    ==>
    RX_STATE_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  MATCH_MP_TAC RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  MATCH_MP_TAC rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_NEXT_STATE_WRITE_CP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)


(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_17set_sop_eop_overrun_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_17set_sop_eop_overrun_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
  ASM_REWRITE_TAC [RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NEXT_RX_STATE_rx_clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17clear_sop_owner_and_hdp_NO_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_NO_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  MATCH_MP_TAC (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``))) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   MATCH_MP_TAC rx_17set_sop_eop_overrun_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   EXISTS_TAC ``env : environment`` THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC rx_17clear_sop_owner_and_hdp_NO_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   EXISTS_TAC ``env : environment`` THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_17set_sop_eop_overrun_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_17set_sop_eop_overrun_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
  ASM_REWRITE_TAC [RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NEXT_RX_STATE_rx_clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17clear_sop_owner_and_hdp_NO_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_NO_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def] THEN
  MATCH_MP_TAC (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``))) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   MATCH_MP_TAC rx_17set_sop_eop_overrun_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   EXISTS_TAC ``env : environment`` THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC rx_17clear_sop_owner_and_hdp_NO_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
   EXISTS_TAC ``nic : nic_state`` THEN
   EXISTS_TAC ``env : environment`` THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_RW_ASM_TAC ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic = rx_18clear_sop_owner_and_hdp nic`` ``nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``x = y`` ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'`` THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_WRITES_BD_QUEUE_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_CURRENT_BD_PA_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_17set_sop_eop_overrun_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_lemma = store_thm (
  "rx_17set_sop_eop_overrun_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun
    ==>
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_WRITE_CP_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_NO_OVERRUN_IMP_NEXT_STATE_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_RX_OVERRUN_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(*******************************************)
(**Start of Lemmas for BD_QUEUE_NO_OVERLAP**)
(*******************************************)

val rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma  )) THEN
  ASM_REWRITE_TAC []);

val rx_17clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma",
  ``!nic env.
    ~nic.rx.overrun
    ==>
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA
      (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def] THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def] THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_RW_ASM_TAC ``f1 a1 a2 = f2 a1`` ``f1 a1 a2`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*****************************************)
(**End of Lemmas for BD_QUEUE_NO_OVERLAP**)
(*****************************************)

(*************************************************)
(**Start of Lemmas for BD_QUEUE_LOCATION_DEFINED**)
(*************************************************)

val rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env`` THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_RW_ASM_TAC ``f1 a1 a2 = f2 a1`` ``f1 a1 a2`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(***********************************************)
(**End of Lemmas for BD_QUEUE_LOCATION_DEFINED**)
(***********************************************)


(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

(* Overrun *)

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_BD_QUEUE
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
   MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
   MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC []
   ,
   Cases_on `e = nic.rx.sop_bd_pa` THENL
   [
    ASM_REWRITE_TAC [] THEN
    ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
    MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma THEN
    RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
    ASM_REWRITE_TAC [] THEN
    ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
    MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  BETA_TAC THEN
  Cases_on `env.rx.sop_eop_both_overrun` THEN
  REWRITE_TAC [stateTheory.overrun_case_case_def] THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THENL
  [
   MATCH_MP_TAC RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
   PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
   EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_NOT_MEM_EOP_UNSEEN_BD_QUEUE_lemma THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
   PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
   EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma THEN
   ASM_REWRITE_TAC []
   ,
   Cases_on `e = nic.rx.sop_bd_pa` THENL
   [
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma THEN
    RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
    PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
    EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
    RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_NOT_MEM_EOP_UNSEEN_BD_QUEUE_lemma THEN
    RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
    PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
    EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
    RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_set_sop_eop_overrun_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_set_sop_eop_overrun_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_SEEN_BD_QUEUE
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    nic.rx.overrun
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)
    (MAP SND (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_set_sop_eop_overrun_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic env.
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_SUBINVARIANT_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_PRESERVES_RX_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17set_sop_eop_overrun_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

val rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_17set_sop_eop_overrun_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_EQ_BETA_lemma] THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_RX_SEEN_BDs_PRESERVES_WELL_DEFINED_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

(* No overrun *)

val rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic) /\
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_RX_SEEN_BDs_PRESERVES_WELL_DEFINED_RX_UNSEEN_BD_QUEUE_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma)) THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

(************************************************)
(**Start of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(************************************************)

val RX_NOT_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_NOT_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic env.
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma)) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE rx_18clear_sop_owner_and_hdp nic`` NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def THEN
  ASM_REWRITE_TAC []);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   MATCH_MP_TAC RX_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC RX_NOT_OVERRUN_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def = Define `
  rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic =
  [(clear_own, nic.rx.sop_bd_pa)]`;

val rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma",
  ``!nic.
    rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic
    =
    rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic``,
  REWRITE_TAC [rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def]);

val rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    ~nic.rx.overrun
    ==>
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_EQ_rx_18clear_sop_owner_and_hdp_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_WRITES_CPPI_RAM_lemma]);

val rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic env.
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma] THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val rx_17clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
    (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  REWRITE_TAC [rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_17clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    ~nic.rx.overrun /\
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [rx_17clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def = Define `
  rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas env nic =
  if nic.rx.overrun then
    rx_17set_sop_eop_overrun_cppi_ram_write_step_bd_pas env nic
  else
    rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`;

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas env nic)
    (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.overrun` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17set_sop_eop_overrun_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def]
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_17clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def]
  ]);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_SEEN_BD_QUEUE
    (MAP SND (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma] THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_SEEN_BD_QUEUE
    (MAP SND (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  COND_CASES_TAC THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_set_sop_eop_overrun_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_17clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_17clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    ~nic.rx.overrun
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    (MAP SND (rx_17clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_17clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma)) THEN
  ASM_REWRITE_TAC [rx_17clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas env nic)
    (MAP SND (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas env nic))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  COND_CASES_TAC THENL
  [
   MATCH_MP_TAC rx_17set_sop_eop_overrun_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC rx_17clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env)
    nic
    (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma] THEN
  MATCH_MP_TAC RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_cppi_ram_write_step_bd_pas_IN_RX_SEEN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(**********************************************)
(**End of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(**********************************************)

val _ = export_theory();
