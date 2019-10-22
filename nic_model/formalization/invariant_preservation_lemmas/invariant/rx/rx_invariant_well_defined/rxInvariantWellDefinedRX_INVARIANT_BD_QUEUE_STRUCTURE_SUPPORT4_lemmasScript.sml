open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open rx_state_definitionsTheory;
open rx_transition_definitionsTheory;
open rx_state_lemmasTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmas";

(* This lemma is useful for a transition function describing operations where
   current_bd_pa, sop_bd_pa and CPPI_RAM are not modified.

   0, 1 and 2 preserves current_bd_pa, sop_bd_pa and CPPI_RAM.
   19 Preserves current_bd_pa, sop_bd_pa and CPPI_RAM.
 *)
val NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic_delta nic'.
    (RX_STATE_RECEIVE_FRAME nic \/
     RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic \/
     RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY nic) /\
    (nic' = nic_delta nic) /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``P \/ Q`` ``P ==> Q`` THEN
  MATCH_MP_TAC (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``))) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic`` NIC_DELTA_PRESERVES_CPPI_RAM_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``(nic_delta : nic_delta_type) nic``] EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(* This lemma is useful for a transition function describing operations where
   current_bd_pa and sop_bd_pa are not modified, but CPPI_RAM is written.

   3 and 4 writes CPPI_RAM at current_bd_pa.
   5 when RX_FRAME_STORED nic.rx \/ LAST_BD nic.rx.current_bd: Writes CPPI_RAM at current_bd_pa.
   6-16 writes CPPI_RAM
   17 when nic.rx.overrun: Writes CPPI_RAM only.
*)
val NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_WRITES_BD_QUEUE_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_WRITES_BD_QUEUE_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (nic' = nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_NIC_DELTA_PRESERVES_RX_BD_QUEUE_lemma)) THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  MATCH_MP_TAC (DISCH ``P : bool`` (DISCH ``Q : bool`` (ASSUME ``P : bool``))) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_BD_QUEUE nic_delta nic`` NIC_DELTA_PRESERVES_RX_BD_QUEUE_def THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  RW_ASM_TAC ``P ==> Q`` RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def THEN
  RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def THEN
  ASM_RW_ASM_TAC ``P \/ Q`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

(* This lemma is useful for a transition function describing operations where
   sop_bd_pa is not modified and current_bd_pa is advanced to current_bd.ndp and
   CPPI_RAM is written.

   5 has two cases: ~(RX_FRAME_STORED nic.rx \/ LAST_BD nic.rx.current_bd): Writes CPPI_RAM at current_bd_pa and advances current_bd_pa to current_bd.ndp
*)
val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_NIC_DELTA_PRESERVES_CURRENT_BD_PA_IN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_NIC_DELTA_PRESERVES_CURRENT_BD_PA_IN_BD_QUEUE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (nic' = nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    ~LAST_BD nic.rx.current_bd /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_NIC_DELTA_PRESERVES_RX_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``~LAST_BD nic.rx.current_bd`` CPPI_RAMTheory.LAST_BD_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_NDP_UNSEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``nic.rx.current_bd.ndp``] RX_INVARIANT_BD_QUEUE_STRUCTURE_MEM_UNSEEN_IMP_MEM_BD_QUEUE_lemma)) THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  RW_ASM_TAC ``NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA nic_delta nic`` NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_def THEN
  REFLECT_ASM_TAC ``(nic_delta nic).rx.current_bd_pa = nic.rx.current_bd.ndp`` THEN
  ASM_RW_ASM_TAC ``nic.rx.current_bd.ndp = (nic_delta nic).rx.current_bd_pa`` ``MEM nic.rx.current_bd.ndp (rx_bd_queue nic)`` THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_BD_QUEUE nic_delta nic`` NIC_DELTA_PRESERVES_RX_BD_QUEUE_def THEN
  REFLECT_ASM_TAC ``rx_bd_queue (nic_delta nic) = rx_bd_queue nic`` THEN
  ASM_RW_ASM_TAC ``rx_bd_queue nic = rx_bd_queue (nic_delta nic)`` ``MEM (nic_delta nic).rx.current_bd_pa (rx_bd_queue nic)`` THEN
  ASM_REWRITE_TAC []);

(* This lemma is useful for a transition function describing operations where
   sop_bd_pa is not modified and current_bd_pa is advanced to current_bd.ndp and
   CPPI_RAM is written.

  17 and ~nic.rx.overrun: Advances sop_bd_pa and current_bd_pa to current_bd.ndp, writes CPPI_RAM and sets next state to write_cp.
  18: Avances sop_bd_pa and current_bd_pa to current_bd.ndp, writes CPPI_RAM and sets next state to write_cp.
*)
val NIC_DELTA_SETS_SOP_BD_PA_CURRENT_BD_PA_TO_CURRENT_BD_NDP_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "NIC_DELTA_SETS_SOP_BD_PA_CURRENT_BD_PA_TO_CURRENT_BD_NDP_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    ((nic_delta nic).rx.current_bd_pa = (nic_delta nic).rx.sop_bd_pa) /\
    RX_STATE_WRITE_CP (nic_delta nic)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE (nic_delta nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_KEEP_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic_delta : nic_delta_type``, ``nic : nic_state``, ``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA nic_delta nic`` NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_def THEN
  COPY_ASM_TAC ``(nic_delta nic).rx.current_bd_pa = (nic_delta nic).rx.sop_bd_pa`` THEN
  ASM_RW_ASM_TAC ``(nic_delta nic).rx.current_bd_pa = nic.rx.current_bd.ndp`` ``(nic_delta nic).rx.current_bd_pa = (nic_delta nic).rx.sop_bd_pa`` THEN
  REFLECT_ASM_TAC ``nic.rx.current_bd.ndp = (nic_delta nic).rx.sop_bd_pa`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``(nic_delta : nic_delta_type) nic``] RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``(nic_delta nic).rx.sop_bd_pa = nic.rx.current_bd.ndp`` THEN
  ASM_REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  ASSUME_TAC (UNDISCH (SPEC ``(nic_delta : nic_delta_type) nic`` RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``~RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM (nic_delta nic)`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def THEN
  RW_ASM_TAC ``~(P \/ Q)`` boolTheory.DE_MORGAN_THM THEN
  REWRITE_TAC [RX_STATE_RECEIVE_FRAME_def] THEN
  ASSUME_TAC (UNDISCH (SPEC ``(nic_delta : nic_delta_type) nic`` RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``(nic_delta : nic_delta_type) nic`` RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_FETCH_NEXT_BD_lemma)) THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY_def, RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue (nic_delta : nic_delta_type nic)``, ``(nic_delta : nic_delta_type nic).rx.sop_bd_pa``, ``(nic_delta : nic_delta_type nic).regs.CPPI_RAM``] bd_queueTheory.BD_QUEUE_START_BD_PA_NEQ_ZERO_IMP_MEM_START_BD_PA_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

