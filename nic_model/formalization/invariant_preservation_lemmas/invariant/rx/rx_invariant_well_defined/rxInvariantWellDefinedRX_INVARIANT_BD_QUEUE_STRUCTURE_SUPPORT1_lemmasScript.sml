open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT1_lemmas";

(* This lemma is useful for transition functions returning a state not satisfying
   RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM (i.e. idle, fetch_next_bd or write_cp)
 *)
val NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma = store_thm (
  "NOT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma",
  ``!nic.
    ~RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

(* This lemma is useful for a transition function describing operations from a state not being
   idle, fetch_next_bd nor write_cp, and where current_bd.ndp, current_bd_pa and CPPI_RAM are
   not modified.
 *)
val NIC_DELTA_PRESERVES_STATE_ISSUE_MEMORY_REQUEST_AND_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "NIC_DELTA_PRESERVES_STATE_ISSUE_MEMORY_REQUEST_AND_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic nic_delta nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (nic' = nic_delta nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic' /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVES_NDP_lemma = store_thm (
  "NIC_DELTA_PRESERVES_NDP_lemma",
  ``!nic_delta nic q start_bd_pa cppi_ram_write_step_bd_pas bd_pa.
    BD_QUEUE q start_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    MEM bd_pa q
    ==>
    (read_ndp bd_pa (nic_delta nic).regs.CPPI_RAM = read_ndp bd_pa nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  MATCH_MP_TAC bd_queueTheory.BD_QUEUE_MEM_IMP_EQ_NEXT_BD_PA_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  EXISTS_TAC ``start_bd_pa : bd_pa_type`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVES_NDP_AT_CURRENT_BD_PA_lemma = store_thm (
  "NIC_DELTA_PRESERVES_NDP_AT_CURRENT_BD_PA_lemma",
  ``!nic_delta nic q start_bd_pa cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic)
    ==>
    (read_ndp nic.rx.current_bd_pa (nic_delta nic).regs.CPPI_RAM = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_NDP_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  EXISTS_TAC ``nic.rx.sop_bd_pa`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

(* This lemma is useful for a transition function describing operations from a state not being
   idle, fetch_next_bd nor write_cp, and where current_bd.ndp and current_bd_pa are not modified
   and the next descriptor pointer is not modified.
 *)
val NIC_DELTA_WRITES_CPPI_RAM_AND_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "NIC_DELTA_WRITES_CPPI_RAM_AND_PRESERVES_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic nic_delta nic' cppi_ram_write_step_bd_pas.
    (nic' = nic_delta nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic`` NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  REFLECT_ASM_TAC ``(nic_delta nic).rx.current_bd.ndp = nic.rx.current_bd.ndp`` THEN
  ASM_RW_ASM_TAC ``nic.rx.current_bd.ndp = (nic_delta nic).rx.current_bd.ndp`` ``nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  REFLECT_ASM_TAC ``(nic' : nic_state) = nic_delta nic`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic_delta nic = nic'`` ``(nic_delta nic).rx.current_bd.ndp = x`` THEN
  ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
  REFLECT_ASM_TAC ``nic_delta nic = (nic' : nic_state)`` THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_NDP_AT_CURRENT_BD_PA_lemma THEN
  EXISTS_TAC ``q : 'a`` THEN
  EXISTS_TAC ``start_bd_pa : 'b`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

