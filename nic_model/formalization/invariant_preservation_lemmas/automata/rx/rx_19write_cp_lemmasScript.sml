open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rx_state_definitionsTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT1_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedTheory;
open rx_transition_definitionsTheory;
open it_state_definitionsTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open rx_state_lemmasTheory;

val _ = new_theory "rx_19write_cp_lemmas";

val rx_19write_cp_NOT_MODIFIED_lemma = store_thm (
  "rx_19write_cp_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.rx.state = rx_idle) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead) /\
    (nic'.it.state = nic.it.state) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_19write_cp_def] THEN
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
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors] THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_19write_cp_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_19write_cp_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA (rx_19write_cp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [rx_19write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_19write_cp_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_19write_cp_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_RX_SOP_BD_PA (rx_19write_cp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_19write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_19write_cp_PRESERVES_CPPI_RAM_lemma = store_thm (
  "rx_19write_cp_PRESERVES_CPPI_RAM_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_CPPI_RAM (rx_19write_cp env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  REWRITE_TAC [rx_19write_cp_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors]);

(* Start of lemmas regarding preservation of RX_INVARIANT_BD_QUEUE_STRUCTURE. *)

val RX_STATE_WRITE_CP_RX_STATE_IDLE_EQ_SOP_BD_PA_CPPI_RAM_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CP_RX_STATE_IDLE_EQ_SOP_BD_PA_CPPI_RAM_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_STATE_WRITE_CP nic /\
    RX_STATE_IDLE nic' /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def, RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def, stateTheory.rx_abstract_state_case_def]);

(* End of lemmas regarding preservation of RX_INVARIANT_BD_QUEUE_STRUCTURE. *)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_19write_cp_IMP_NEXT_STATE_IDLE_lemma = store_thm (
  "rx_19write_cp_IMP_NEXT_STATE_IDLE_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic)
    ==>
    RX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_19write_cp_def] THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  MATCH_MP_TAC RX_STATE_IDLE_IMP_NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  MATCH_MP_TAC rx_19write_cp_IMP_NEXT_STATE_IDLE_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic) /\
    RX_STATE_WRITE_CP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (GEN_ALL (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``)))) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_NOT_MODIFIED_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CP nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic) /\
    RX_STATE_WRITE_CP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (GEN_ALL (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``)))) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_NOT_MODIFIED_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CP nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_19write_cp_NOT_IT_STATE_INITIALIZED_OR_BD_QUEUE_EMPTY_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_19write_cp_NOT_IT_STATE_INITIALIZED_OR_BD_QUEUE_EMPTY_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic) /\
    (~IT_STATE_INITIALIZED nic \/ RX_BD_QUEUE_EMPTY nic) /\
    RX_STATE_WRITE_CP nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_NOT_MODIFIED_lemma)) THEN
  WEAKEN_TAC is_eq THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``nic'.rx.state = rx_idle`` (GSYM RX_STATE_IDLE_def) THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_STATE_RECEIVE_FRAME_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY_def] THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.DE_MORGAN_THM] (CONTRAPOS (SPEC ``nic' : nic_state`` RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_STATE_IDLE_AND_NOT_RX_STATE_WRITE_CP_lemma))) THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_IDLE nic'`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [boolTheory.NOT_CLAUSES] (CONTRAPOS (SPEC ``nic' : nic_state`` RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_IDLE_lemma)))) THEN
  Cases_on `¬IT_STATE_INITIALIZED nic` THENL
  [
   RW_ASM_TAC ``~IT_STATE_INITIALIZED nic`` IT_STATE_INITIALIZED_def THEN
   REFLECT_ASM_TAC ``nic'.it.state = nic.it.state`` THEN
   ASM_RW_ASM_TAC ``nic.it.state = nic'.it.state`` ``nic.it.state ≠ init_initialized`` THEN
   RW_ASM_TAC ``nic'.it.state ≠ init_initialized`` (GSYM IT_STATE_INITIALIZED_def) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~~IT_STATE_INITIALIZED nic`` ``P \/ Q`` THEN
   RW_ASM_TAC ``RX_BD_QUEUE_EMPTY nic`` RX_BD_QUEUE_EMPTY_def THEN
   ASM_RW_ASM_TAC ``nic.rx.sop_bd_pa = 0w`` ``nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa`` THEN
   RW_ASM_TAC ``nic'.rx.sop_bd_pa = 0w`` (GSYM RX_BD_QUEUE_EMPTY_def) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_19write_cp_NOT_BD_QUEUE_EMPTY_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_19write_cp_NOT_BD_QUEUE_EMPTY_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic) /\
    ~RX_BD_QUEUE_EMPTY nic /\
    RX_STATE_WRITE_CP nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_19write_cp env`` THEN
  REWRITE_TAC [rx_19write_cp_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_19write_cp_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_19write_cp_PRESERVES_CPPI_RAM_lemma] THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY_def] THEN
  ASM_REWRITE_TAC []);

val rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic) /\
    RX_STATE_WRITE_CP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `~IT_STATE_INITIALIZED nic \/ RX_BD_QUEUE_EMPTY nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_19write_cp_NOT_IT_STATE_INITIALIZED_OR_BD_QUEUE_EMPTY_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   RW_ASM_TAC ``~P`` boolTheory.DE_MORGAN_THM THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_19write_cp_NOT_BD_QUEUE_EMPTY_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_19write_cp_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_IDLE_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_IMP_NEXT_STATE_IDLE_lemma)) THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

val rx_19write_cp_PRESERVES_UNSEEN_BD_QUEUE_lemma = store_thm (
  "rx_19write_cp_PRESERVES_UNSEEN_BD_QUEUE_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic) /\
    RX_STATE_WRITE_CP nic
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_IMP_NEXT_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CP_RX_STATE_IDLE_EQ_SOP_BD_PA_CPPI_RAM_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

(************************************************)
(**Start of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(************************************************)

val RX_STATE_WRITE_CP_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_WRITE_CP_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic env.
    RX_STATE_WRITE_CP nic
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (rx_19write_cp env) nic``,
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_19write_cp env nic``] rx_19write_cp_PRESERVES_UNSEEN_BD_QUEUE_lemma)]);

val rx_19write_cp_cppi_ram_write_step_bd_pas_def = Define `
  rx_19write_cp_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val rx_19write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_19write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rx_19write_cp env) 
    nic
    rx_19write_cp_cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [rx_19write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_19write_cp env nic``] rx_19write_cp_NOT_MODIFIED_lemma)]);

val rx_19write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma = store_thm (
  "rx_19write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma",
  ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_19write_cp_cppi_ram_write_step_bd_pas
    (MAP SND rx_19write_cp_cppi_ram_write_step_bd_pas)``,
  REWRITE_TAC [rx_19write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val rx_19write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_19write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION rx_19write_cp_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [rx_19write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_19write_cp env)
    nic
    rx_19write_cp_cppi_ram_write_step_bd_pas (MAP SND rx_19write_cp_cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_19write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_19write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma] THEN
  REWRITE_TAC [rx_19write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_19write_cp_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_19write_cp_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic. BD_PAs_IN_RX_SEEN_BD_QUEUE (MAP SND rx_19write_cp_cppi_ram_write_step_bd_pas) nic``,
  GEN_TAC THEN
  REWRITE_TAC [rx_19write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [EMPTY_IN_RX_SEEN_BD_QUEUE_lemma]);

val rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    (rx_19write_cp env)
    nic
    rx_19write_cp_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_19write_cp_IN_RX_SEEN_BD_QUEUE_lemma]);

(**********************************************)
(**End of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(**********************************************)

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val rx_19write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_19write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_19write_cp_cppi_ram_write_step_bd_pas
    (rx_bd_queue nic)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_19write_cp_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_19write_cp_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      (rx_19write_cp env)
      nic
      rx_19write_cp_cppi_ram_write_step_bd_pas
      (rx_bd_queue nic)``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_19write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_19write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_19write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)
val _ = export_theory();

