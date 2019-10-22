open HolKernel Parse boolLib bossLib;
open helperTactics;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open bd_listTheory;
open rxInvariantWellDefinedTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_NO_OVERLAP_lemmas";

(* Lemma for the case when nic.rx.sop_bd_pa is unmodified and nic.regs.CPPI_RAM
   is unmodified: nic_delta 0, 1, 2, 19. *)
val NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "NIC_DELTA_PRESERVES_RX_SOP_BD_PA_CPPI_RAM_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic nic_delta nic'.
    (nic' = nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def, NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REFLECT_ASM_TAC ``nic' = (nic_delta : nic_delta_type) nic`` THEN
  KEEP_ASM_RW_ASM_TAC ``(nic_delta : nic_delta_type) nic = nic'`` ``(f a).rx.sop_bd_pa = y`` THEN
  ASM_RW_ASM_TAC ``(nic_delta : nic_delta_type) nic = nic'`` ``(f a).regs.CPPI_RAM = y`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(* Lemma for the case when nic.rx.sop_bd_pa is unmodified and nic.regs.CPPI_RAM
   is written: nic_delta 3-16, 17 and overrun. *)
val NIC_DELTA_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "NIC_DELTA_PRESERVES_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic nic_delta nic' cppi_ram_write_step_bd_pas.
    (nic' = nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic_delta : nic_delta_type``, ``nic : nic_state``, ``rx_bd_queue nic``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic : nic_state``, ``(nic_delta : nic_delta_type) nic``] BD_QUEUE_SAME_Q_IMP_EQ_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(* Lemma for the case when nic.rx.sop_bd_pa is assigned nic.rx.current_bd.ndp
   and CPPI_RAM is written: nic_delta 17 and not overrun, 18. *)
val NIC_DELTA_ASSIGNS_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma = store_thm (
  "NIC_DELTA_ASSIGNS_RX_SOP_BD_PA_SUBINVARIANT_PRESERVES_BD_QUEUE_NO_OVERLAP_lemma",
  ``!nic nic_delta nic' cppi_ram_write_step_bd_pas.
    (nic' = nic_delta nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_NOT_EXPAND_RX_BD_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x : bd_pa_type list. P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASM_RW_ASM_TAC ``q = q' ++ q''`` ``~BD_LIST_OVERLAP (rx_bd_queue nic)`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : bd_pa_type list``, ``rx_bd_queue (nic_delta : nic_delta_type nic)``] NOT_BD_LIST_OVERLAP_APPEND_IMP_NOT_BD_LIST_OVERLAP_SUFFIX_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def]);

val _ = export_theory();

