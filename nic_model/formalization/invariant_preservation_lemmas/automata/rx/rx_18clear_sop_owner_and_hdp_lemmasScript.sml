open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedLemmasTheory;
open bd_listTheory;
open clear_own_lemmasTheory;
open rx_state_lemmasTheory;
open rx_state_definitionsTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT1_lemmasTheory;
open rx_bd_queueTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemmasTheory;

val _ = new_theory "rx_18clear_sop_owner_and_hdp_lemmas";

val rx_18clear_sop_owner_and_hdp_NOT_MODIFIED_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_NOT_MODIFIED_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn term => true) THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_18clear_sop_owner_and_hdp_UPDATES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_UPDATES_RX_SOP_BD_PA_lemma",
  ``!nic. ((rx_18clear_sop_owner_and_hdp nic).rx.sop_bd_pa = nic.rx.current_bd.ndp)``,
  GEN_TAC THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def = Define `
  rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic = [(clear_own, nic.rx.sop_bd_pa)]`;

val MEM_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "MEM_rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_lemma",
  ``!nic bd_pa.
    MEM bd_pa (MAP SND (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))
    ==>
    (bd_pa = nic.rx.sop_bd_pa)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def, listTheory.MAP] THEN
   REWRITE_TAC [listTheory.MEM]);

val rx_18clear_sop_owner_and_hdp_WRITES_CPPI_RAM_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_WRITES_CPPI_RAM_lemma",
  ``!nic.
    ((rx_18clear_sop_owner_and_hdp nic).regs.CPPI_RAM =
     cppi_ram_write nic.regs.CPPI_RAM (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))``,
  GEN_TAC THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors] THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_18clear_sop_owner_and_hdp_CPPI_RAM_EQ_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_CPPI_RAM_EQ_lemma",
  ``!nic.
    cppi_ram_write nic.regs.CPPI_RAM (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    =
    clear_own nic.regs.CPPI_RAM nic.rx.sop_bd_pa``,
  GEN_TAC THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma",
  ``!nic.
    MAP SND (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic) = [nic.rx.sop_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma",
  ``!nic. MAP FST (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic) = [clear_own]``,
  GEN_TAC THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    rx_18clear_sop_owner_and_hdp
    nic
    (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_WRITES_CPPI_RAM_lemma]);

val rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma)) THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma] THEN
  MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
  ASM_REWRITE_TAC []);

val rx_18clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
    (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  REWRITE_TAC [clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]);

val rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE rx_18clear_sop_owner_and_hdp nic (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic) (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_18clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE rx_18clear_sop_owner_and_hdp nic (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic) (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val rx_18clear_sop_owner_and_hdp_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa (rx_18clear_sop_owner_and_hdp nic).regs.CPPI_RAM``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`` THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma]);

val rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_FINITE_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
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
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_18clear_sop_owner_and_hdp_PRESERVES_RX_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``r = f a`` THEN
  KEEP_ASM_RW_ASM_TAC ``f a = r`` ``BD_QUEUE q address (f a).regs.CPPI_RAM`` THEN
  ASSUME_TAC (SPEC_ALL rx_18clear_sop_owner_and_hdp_UPDATES_RX_SOP_BD_PA_lemma) THEN
  ASM_RW_ASM_TAC ``rx_18clear_sop_owner_and_hdp nic = nic'`` ``(rx_18clear_sop_owner_and_hdp nic).rx.sop_bd_pa = nic.rx.current_bd.ndp`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);


(*Start of lemmas for RX_INVARIANT_BD_QUEUE_STRUCTURE*)
val rx_18clear_sop_owner_and_hdp_NEXT_STATE_rx_write_cp_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_NEXT_STATE_rx_write_cp_lemma",
  ``!nic. (rx_18clear_sop_owner_and_hdp nic).rx.state = rx_write_cp``,
  GEN_TAC THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_18clear_sop_owner_and_hdp_NEXT_STATE_RX_STATE_WRITE_CP_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_NEXT_STATE_RX_STATE_WRITE_CP_lemma",
  ``!nic. RX_STATE_WRITE_CP (rx_18clear_sop_owner_and_hdp nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def, rx_18clear_sop_owner_and_hdp_NEXT_STATE_rx_write_cp_lemma]);

(*End of lemmas for RX_INVARIANT_BD_QUEUE_STRUCTURE*)





(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_18clear_sop_owner_and_hdp_IMP_NEXT_STATE_WRITE_CP_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_IMP_NEXT_STATE_WRITE_CP_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic)
    ==>
    RX_STATE_WRITE_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);
    
val rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  MATCH_MP_TAC RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_IMP_NEXT_STATE_WRITE_CP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  MATCH_MP_TAC (GEN_ALL (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``)))) THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def] THEN
  MATCH_MP_TAC (GEN_ALL (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``)))) THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_lemma",
  ``!nic. NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA rx_18clear_sop_owner_and_hdp nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_18clear_sop_owner_and_hdp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma",
  ``!nic. (rx_18clear_sop_owner_and_hdp nic).rx.current_bd_pa = (rx_18clear_sop_owner_and_hdp nic).rx.sop_bd_pa``,
  GEN_TAC THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
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
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_SETS_SOP_BD_PA_CURRENT_BD_PA_TO_CURRENT_BD_NDP_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`` THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_NEXT_STATE_RX_STATE_WRITE_CP_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

val rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic /\
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
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_WRITE_CP_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_NEXT_STATE_RX_STATE_WRITE_CP_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)
  
(*******************************************)
(**Start of Lemmas for BD_QUEUE_NO_OVERLAP**)
(*******************************************)

val rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma",
  ``!nic. NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA rx_18clear_sop_owner_and_hdp nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_ASSIGNS_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp`` THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`` THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma] THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(*****************************************)
(**End of Lemmas for BD_QUEUE_NO_OVERLAP**)
(*****************************************)

(************************************************)
(**Start of Lemmas for BD_QUEUE_LOCATION_DEFNED**)
(************************************************)

val rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic nic'.
    (nic' = rx_18clear_sop_owner_and_hdp nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_ASSIGNS_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_LOCATION_DEFINED_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp`` THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`` THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma] THEN
  MATCH_MP_TAC rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(***********************************************)
(**End of Lemmas for BD_QUEUE_LOCATION_DEFINED**)
(***********************************************)

(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_BD_QUEUE
    (MAP SND (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))
    nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE
    (MAP SND (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))
    nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_SEEN_BD_QUEUE
    (MAP SND (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))
    nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_18clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_18clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    rx_18clear_sop_owner_and_hdp nic
    (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)
    (MAP SND (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic))``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    rx_18clear_sop_owner_and_hdp
    nic
    (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma]);

val RX_STATE_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    rx_18clear_sop_owner_and_hdp
    nic
    (rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE rx_18clear_sop_owner_and_hdp nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_18clear_sop_owner_and_hdp_cppi_ram_write_step_bd_pas nic`` THEN
  REWRITE_TAC [rx_18clear_sop_owner_and_hdp_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_18clear_sop_owner_and_hdp_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [rx_18clear_sop_owner_and_hdp_NEXT_STATE_RX_STATE_WRITE_CP_lemma]);

val RX_STATE_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_CLEAR_SOP_OWNER_AND_HDP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic.
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE rx_18clear_sop_owner_and_hdp nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

val _ = export_theory();
