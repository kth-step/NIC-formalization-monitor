open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open rx_bd_queueTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open rx_state_definitionsTheory;
open rx_state_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedLemmasTheory;
open bd_listTheory;
open set_sop_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT1_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT2_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;

val _ = new_theory "rx_11set_sop_sop_lemmas";

val rx_11set_sop_sop_NOT_MODIFIED_lemma = store_thm (
  "rx_11set_sop_sop_NOT_MODIFIED_lemma",
  ``!nic nic'.
    (nic' = rx_11set_sop_sop nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
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
  REWRITE_TAC [rx_11set_sop_sop_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates, combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_11set_sop_sop_NOT_MODIFIED_EQ_lemma = store_thm (
  "rx_11set_sop_sop_NOT_MODIFIED_EQ_lemma",
  ``!nic. ((rx_11set_sop_sop nic).rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  GEN_TAC THEN
  REWRITE_TAC [(REWRITE_RULE [] (SPECL [``nic : nic_state``, ``rx_11set_sop_sop nic``] rx_11set_sop_sop_NOT_MODIFIED_lemma))]);

val rx_11set_sop_sop_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_11set_sop_sop_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic. NIC_DELTA_PRESERVES_RX_SOP_BD_PA rx_11set_sop_sop nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_NOT_MODIFIED_EQ_lemma]);

val rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def = Define `
  rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic = [(set_sop, nic.rx.sop_bd_pa)]`;

val MEM_rx_11set_sop_sop_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "MEM_rx_11set_sop_sop_cppi_ram_write_step_bd_pas_lemma",
  ``!nic bd_pa.
    MEM bd_pa (MAP SND (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic))
    ==>
    (bd_pa = nic.rx.sop_bd_pa)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def, listTheory.MAP] THEN
   REWRITE_TAC [listTheory.MEM]);

val rx_11set_sop_sop_WRITES_CPPI_RAM_lemma = store_thm (
  "rx_11set_sop_sop_WRITES_CPPI_RAM_lemma",
  ``!nic.
    (rx_11set_sop_sop nic).regs.CPPI_RAM =
    cppi_ram_write nic.regs.CPPI_RAM (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_def] THEN
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

val rx_11set_sop_sop_CPPI_RAM_EQ_lemma = store_thm (
  "rx_11set_sop_sop_CPPI_RAM_EQ_lemma",
  ``!nic.
    cppi_ram_write nic.regs.CPPI_RAM (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)
    =
    set_sop nic.regs.CPPI_RAM nic.rx.sop_bd_pa``,
  GEN_TAC THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma]);

val rx_11set_sop_sop_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma = store_thm (
  "rx_11set_sop_sop_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma",
  ``!nic. MAP SND (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic) = [nic.rx.sop_bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_11set_sop_sop_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma = store_thm (
  "rx_11set_sop_sop_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma",
  ``!nic. MAP FST (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic) = [set_sop]``,
  GEN_TAC THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_11set_sop_sop_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_11set_sop_sop_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    rx_11set_sop_sop
    nic
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [SPEC_ALL rx_11set_sop_sop_WRITES_CPPI_RAM_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write1_EQ_REVERSE_lemma]);

val rx_11set_sop_sop_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_11set_sop_sop_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)
    (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_STATE_SET_SOP_SOP nic`` RX_STATE_SET_SOP_SOP_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_set_sop_sop_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma)) THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma] THEN
  MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
  ASM_REWRITE_TAC []);

val rx_11set_sop_sop_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_11set_sop_sop_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  REWRITE_TAC [set_sop_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]);

val rx_11set_sop_sop_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_11set_sop_sop_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE rx_11set_sop_sop nic (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic) (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_11set_sop_sop_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_11set_sop_sop_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*
How to prove that q in BD_QUEUE q start_bd_pa CPPI_RAM is preserved:
1. Prove that nic_delta writes CPPI_RAM according to the sequence of
   (cppi_ram_write_step, bd_pa) pairs in cppi_ram_step_bd_pas:
   NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas

DONE: rx_5write_from_port_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma

2. Prove that each bd_pa in cppi_ram_write_step_bd_pas is in q:
   CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def

DONE: rx_5write_from_port_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma

3. Prove that each cppi_ram_write_step in cppi_ram_write_step_bd_pas writes
   the BD at the corresponding address: CPPI_RAM_WRITE_STEP_WRITES_BD_def.

DONE: write_from_port_WRITES_BD_lemma


4. Prove that each cppi_ram_write_step in cppi_ram_write_step_bd_pas
   preserves the NDP field of the BD at the corresponding address:
   CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def.

Done: write_from_port_PRESERVES_NDP_lemma

5. Use 3. and 4. to prove:
   PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def nic_delta

Done: rx_5write_from_port_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma

6. Apply NIC_DELTA_PRESERVES_BD_QUEUE_lemma.
*)
val rx_11set_sop_sop_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "rx_11set_sop_sop_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa (rx_11set_sop_sop nic).regs.CPPI_RAM``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  EXISTS_TAC ``rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic`` THEN
  MATCH_MP_TAC rx_11set_sop_sop_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma]);











(******Start of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE*********)

val rx_11set_sop_sop_CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_lemma = store_thm (
  "rx_11set_sop_sop_CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)
    nic``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_def]);

val RX_STATE_SET_SOP_SOP_IMP_RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_IMP_RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic
    ==>
    RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA
    nic
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_SOP_IMP_RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_lemma]);

val RX_STATE_SET_SOP_SOP_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic
    ==>
    RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA
    nic
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_SOP_IMP_RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_def]);

val rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic.
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA rx_11set_sop_sop nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``rx_11set_sop_sop nic``] rx_11set_sop_sop_NOT_MODIFIED_lemma)]);

val rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_NDP_lemma = store_thm (
  "rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_NDP_lemma",
  ``!nic.
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP rx_11set_sop_sop nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``rx_11set_sop_sop nic``] rx_11set_sop_sop_NOT_MODIFIED_lemma)]);

val rx_11set_sop_sop_NEXT_RX_STATE_rx_write_sop_pass_crc_lemma = store_thm (
  "rx_11set_sop_sop_NEXT_RX_STATE_rx_write_sop_pass_crc_lemma",
  ``!nic.
    rx_write_sop_pass_crc = (rx_11set_sop_sop nic).rx.state``,
  GEN_TAC THEN
  REWRITE_TAC [rx_11set_sop_sop_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_state]);

val rx_11set_sop_sop_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma = store_thm (
  "rx_11set_sop_sop_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM
    (rx_11set_sop_sop nic)``,
  GEN_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_PASS_CRC_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_NEXT_RX_STATE_rx_write_sop_pass_crc_lemma]);

(******End of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE*********)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic nic'.
    (nic' = rx_11set_sop_sop nic) /\
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_CPPI_RAM_AND_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT1_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_11set_sop_sop`` THEN
  EXISTS_TAC ``rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic`` THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_SOP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_11set_sop_sop_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_PA_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic nic'.
    (nic' = rx_11set_sop_sop nic) /\
    RX_STATE_SET_SOP_SOP nic /\
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
  MATCH_MP_TAC RX_STATE_WRITE_SOP_PASS_CRC_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_SOP_PASS_CRC_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_NEXT_RX_STATE_rx_write_sop_pass_crc_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic nic'.
    (nic' = rx_11set_sop_sop nic) /\
    RX_STATE_SET_SOP_SOP nic /\
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
  MATCH_MP_TAC RX_STATE_WRITE_SOP_PASS_CRC_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_SOP_PASS_CRC_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_NEXT_RX_STATE_rx_write_sop_pass_crc_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic'.
    (nic' = rx_11set_sop_sop nic) /\
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
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
  EXISTS_TAC ``rx_11set_sop_sop`` THEN
  EXISTS_TAC ``rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic`` THEN

  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_SOP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_11set_sop_sop_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_SOP_BD_PA_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_11set_sop_sop_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic nic'.
    (nic' = rx_11set_sop_sop nic) /\
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_11set_sop_sop_NOT_MODIFIED_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_SOP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

val RX_STATE_SET_SOP_SOP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_BD_QUEUE
    (MAP SND (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic))
    nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_SET_SOP_SOP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_SET_SOP_SOP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE
    (MAP SND (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic))
    nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_cppi_ram_write_step_bd_pas_def] THEN
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
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_SET_SOP_SOP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_SET_SOP_SOP_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_SEEN_BD_QUEUE
    (MAP SND (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic))
    nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_SOP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_SOP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_11set_sop_sop_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_11set_sop_sop_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    rx_11set_sop_sop nic
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)
    (MAP SND (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic))``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_11set_sop_sop_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val RX_STATE_SET_SOP_SOP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    rx_11set_sop_sop
    nic
    (rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_SOP_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_11set_sop_sop_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma]);

val RX_STATE_SET_SOP_SOP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_SET_SOP_SOP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic.
    RX_STATE_SET_SOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE rx_11set_sop_sop nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_SUBINVARIANT_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_11set_sop_sop_cppi_ram_write_step_bd_pas nic`` THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_11set_sop_sop_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_11set_sop_sop_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_SOP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  REWRITE_TAC [rx_11set_sop_sop_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma] THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

val _ = export_theory();

