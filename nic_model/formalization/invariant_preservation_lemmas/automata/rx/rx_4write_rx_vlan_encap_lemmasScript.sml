open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open rx_bd_queueTheory;
open cppi_ram_writesTheory;
open bd_queue_preservation_lemmasTheory;
open rx_state_definitionsTheory;
open rx_state_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open bd_listTheory;
open write_rx_vlan_encap_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT1_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT2_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;

val _ = new_theory "rx_4write_rx_vlan_encap_lemmas";

val rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma = store_thm (
  "rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rx_4write_rx_vlan_encap env nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
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
  REWRITE_TAC [rx_4write_rx_vlan_encap_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors, stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors]);

val rx_4write_rx_vlan_encap_NOT_MODIFIED_EQ_lemma = store_thm (
  "rx_4write_rx_vlan_encap_NOT_MODIFIED_EQ_lemma",
  ``!nic env.
    ((rx_4write_rx_vlan_encap env nic).rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [(REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_4write_rx_vlan_encap env nic``] rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma))]);

val rx_4write_rx_vlan_encap_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_4write_rx_vlan_encap_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_RX_SOP_BD_PA (rx_4write_rx_vlan_encap env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_4write_rx_vlan_encap env nic``] rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma)]);

val rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def = Define `
  rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic =
  [((\CPPI_RAM bd_pa. write_rx_vlan_encap CPPI_RAM bd_pa env.rx.rx_vlan_encap), nic.rx.current_bd_pa)]`;

val MEM_rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "MEM_rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_lemma",
  ``!nic env bd_pa.
    MEM bd_pa (MAP SND (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic))
    ==>
    (bd_pa = nic.rx.current_bd_pa)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def, listTheory.MAP] THEN
   REWRITE_TAC [listTheory.MEM]);

val rx_4write_rx_vlan_encap_WRITES_CPPI_RAM_lemma = store_thm (
  "rx_4write_rx_vlan_encap_WRITES_CPPI_RAM_lemma",
  ``!nic env.
    ((rx_4write_rx_vlan_encap env nic).regs.CPPI_RAM =
     cppi_ram_write nic.regs.CPPI_RAM (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_def] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `n` THEN
  REWRITE_TAC [stateTheory.nic_regs_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_regs_accessors]);

val rx_4write_rx_vlan_encap_CPPI_RAM_EQ_lemma = store_thm (
  "rx_4write_rx_vlan_encap_CPPI_RAM_EQ_lemma",
  ``!nic env.
    cppi_ram_write nic.regs.CPPI_RAM (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic) = write_rx_vlan_encap nic.regs.CPPI_RAM nic.rx.current_bd_pa env.rx.rx_vlan_encap``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma] THEN
  BETA_TAC THEN
  REWRITE_TAC []);

val rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma = store_thm (
  "rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma",
  ``!nic env.
    MAP SND (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic) =
    [nic.rx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma = store_thm (
  "rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma",
  ``!nic env.
    MAP FST (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic) =
    [\CPPI_RAM bd_pa. write_rx_vlan_encap CPPI_RAM bd_pa env.rx.rx_vlan_encap]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP]);

val rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rx_4write_rx_vlan_encap env)
    nic
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [SPECL [``nic' : nic_state``, ``env : environment``] rx_4write_rx_vlan_encap_WRITES_CPPI_RAM_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write1_EQ_REVERSE_lemma]);

val rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)
    (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_RX_VLAN_ENCAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_write_rx_vlan_encap_IMP_RX_STATE_WRITE_CURRENT_BD_PA_lemma)) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma)))) THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_EQ_BD_PAs_lemma] THEN
  MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
  ASM_REWRITE_TAC []);

val rx_4write_rx_vlan_encap_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_4write_rx_vlan_encap_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic env.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_EQ_cppi_ram_write_steps_lemma] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  REWRITE_TAC [write_rx_vlan_encap_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma]);

val rx_4write_rx_vlan_encap_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_4write_rx_vlan_encap_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE (rx_4write_rx_vlan_encap env) nic (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic) (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*
How to prove that q in BD_QUEUE q start_bd_pa CPPI_RAM is preserved:
1. Prove that nic_delta writes CPPI_RAM according to the sequence of
   (cppi_ram_write_step, bd_pa) pairs in cppi_ram_step_bd_pas:
   NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas

DONE: rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma

2. Prove that each bd_pa in cppi_ram_write_step_bd_pas is in q:
   CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def

DONE: rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma

3. Prove that each cppi_ram_write_step in cppi_ram_write_step_bd_pas writes
   the BD at the corresponding address: CPPI_RAM_WRITE_STEP_WRITES_BD_def.

DONE: write_rx_vlan_encap_WRITES_BD_lemma


4. Prove that each cppi_ram_write_step in cppi_ram_write_step_bd_pas
   preserves the NDP field of the BD at the corresponding address:
   CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def.

Done: write_rx_vlan_encap_PRESERVES_NDP_lemma

5. Use 3. and 4. to prove:
   PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def nic_delta

Done: rx_4write_rx_vlan_encap_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma

6. Apply NIC_DELTA_PRESERVES_BD_QUEUE_lemma.
*)
val rx_4write_rx_vlan_encap_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "rx_4write_rx_vlan_encap_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic env.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic) /\
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa (rx_4write_rx_vlan_encap env nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  EXISTS_TAC ``rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic`` THEN
  MATCH_MP_TAC rx_4write_rx_vlan_encap_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);







(******Start of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE*********)

val rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA_lemma = store_thm (
  "rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA_lemma",
  ``!nic env.
    CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)
    nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP, IN_LIST1_IMP_IN_LIST2_def]);

val RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic
    ==>
    RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA
    nic
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_WRITE_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA_lemma]);

val RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic
    ==>
    RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA
    nic
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_def]);

val rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA (rx_4write_rx_vlan_encap env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_4write_rx_vlan_encap env nic``] rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma)]);

val rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_NDP_lemma = store_thm (
  "rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_NDP_lemma",
  ``!nic env.
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP (rx_4write_rx_vlan_encap env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_4write_rx_vlan_encap env nic``] rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma)]);

val rx_4write_rx_vlan_encap_NEXT_RX_STATE_rx_write_from_port_lemma = store_thm (
  "rx_4write_rx_vlan_encap_NEXT_RX_STATE_rx_write_from_port_lemma",
  ``!nic env.
    rx_write_from_port = (rx_4write_rx_vlan_encap env nic).rx.state``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_state]);

val rx_4write_rx_vlan_encap_NEXT_RX_STATE_WRITE_RX_VLAN_ENCAP_lemma = store_thm (
  "rx_4write_rx_vlan_encap_NEXT_RX_STATE_WRITE_RX_VLAN_ENCAP_lemma",
  ``!nic env.
    RX_STATE_WRITE_FROM_PORT (rx_4write_rx_vlan_encap env nic)``,
  REWRITE_TAC [RX_STATE_WRITE_FROM_PORT_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_NEXT_RX_STATE_rx_write_from_port_lemma]);

val rx_4write_rx_vlan_encap_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma = store_thm (
  "rx_4write_rx_vlan_encap_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma",
  ``!nic env.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM
    ((rx_4write_rx_vlan_encap env) nic)``,
  REPEAT GEN_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_FROM_PORT_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_NEXT_RX_STATE_rx_write_from_port_lemma]);

(******End of lemmas regarding RX_INVARIANT_BD_QUEUE_STRUCTURE*********)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic env nic'.
    (nic' = rx_4write_rx_vlan_encap env nic) /\
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
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
  EXISTS_TAC ``rx_4write_rx_vlan_encap env`` THEN
  EXISTS_TAC ``rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic`` THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_4write_rx_vlan_encap_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_PA_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic env nic'.
    (nic' = rx_4write_rx_vlan_encap env nic) /\
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
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
  MATCH_MP_TAC RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [RX_STATE_WRITE_FROM_PORT_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_NEXT_RX_STATE_rx_write_from_port_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic env nic'.
    (nic' = rx_4write_rx_vlan_encap env nic) /\
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
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
  MATCH_MP_TAC RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_FROM_PORT_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_NEXT_RX_STATE_rx_write_from_port_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_4write_rx_vlan_encap env nic) /\
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
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
  EXISTS_TAC ``rx_4write_rx_vlan_encap env`` THEN
  EXISTS_TAC ``rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic`` THEN  
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_4write_rx_vlan_encap_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_4write_rx_vlan_encap_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic env nic'.
    (nic' = rx_4write_rx_vlan_encap env nic)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  ASM_REWRITE_TAC [rx_4write_rx_vlan_encap_NEXT_RX_STATE_WRITE_RX_VLAN_ENCAP_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

val RX_STATE_WRITE_RX_VLAN_ENCAP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_BD_QUEUE
    (MAP SND (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_RX_VLAN_ENCAP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE
    (MAP SND (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_RX_VLAN_ENCAP_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_PAs_IN_RX_SEEN_BD_QUEUE
    (MAP SND (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic))
    nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_BD_QUEUE_STRUCTURE_SUPPORT_IMP_WRITTEN_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_RX_SUBINVARIANT_IMP_WRITTEN_BD_NOT_IN_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_4write_rx_vlan_encap_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_4write_rx_vlan_encap_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_4write_rx_vlan_encap env) nic
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)
    (MAP SND (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val RX_STATE_WRITE_RX_VLAN_ENCAP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_SUBINVARIANT_IMP_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    (rx_4write_rx_vlan_encap env)
    nic
    (rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_RX_SUBINVARIANT_IMP_WRITTEN_BD_IN_RX_SEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_REFL_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma]);

val RX_STATE_WRITE_RX_VLAN_ENCAP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_WRITE_RX_VLAN_ENCAP_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic env.
    RX_STATE_WRITE_RX_VLAN_ENCAP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (rx_4write_rx_vlan_encap env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_SUBINVARIANT_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_4write_rx_vlan_encap_cppi_ram_write_step_bd_pas env nic`` THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_PRESERVES_RX_CURRENT_BD_NDP_lemma] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_4write_rx_vlan_encap_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  REWRITE_TAC [rx_4write_rx_vlan_encap_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma] THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

val _ = export_theory();

