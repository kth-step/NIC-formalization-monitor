open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open rxTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rx_state_definitionsTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_lemmasTheory;
open rx_state_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT2_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantMemoryWritesTheory;

val _ = new_theory "rx_2issue_next_memory_write_request_lemmas";

val rx_2issue_next_memory_write_request_FST_lemma = store_thm (
  "rx_2issue_next_memory_write_request_FST_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    (nic' = (FST o rx_2issue_next_memory_write_request) nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (SPEC ``rx_2issue_next_memory_write_request nic`` (INST_TYPE [alpha |-> ``: nic_state``, beta |-> ``: memory_request option``] pairTheory.PAIR))] thm)) THEN
  RW_ASM_TAC ``P`` pairTheory.PAIR_EQ THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.rx.current_bd.bp = nic.rx.current_bd.bp) /\
    (nic'.rx.current_bd_size = nic.rx.current_bd_size) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors, stateTheory.nic_state_rx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors, stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [stateTheory.nic_state_accessors, stateTheory.rx_state_accessors]);

val rx_2issue_next_memory_write_request_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic. NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA (FST o rx_2issue_next_memory_write_request) nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_2issue_next_memory_write_request_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic. NIC_DELTA_PRESERVES_RX_SOP_BD_PA (FST o rx_2issue_next_memory_write_request) nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma",
  ``!nic. NIC_DELTA_PRESERVES_CPPI_RAM (FST o rx_2issue_next_memory_write_request) nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  REWRITE_TAC [combinTheory.o_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors]);





val rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma = store_thm (
  "rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors, stateTheory.nic_state_rx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors, stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM]);

val rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_SAME_NEXT_STATE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_SAME_NEXT_STATE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_STORE_MORE_BYTES nic.rx
    ==>
    (nic'.rx.state = nic.rx.state)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
  RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def THEN
  RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NOT_MODIFIED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NOT_MODIFIED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_STORE_MORE_BYTES nic.rx
    ==>
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_SAME_NEXT_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_PACKET_ERROR_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_PACKET_ERROR_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_STATE_WRITE_PACKET_ERROR nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_PACKET_ERROR_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors, stateTheory.nic_state_rx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_accessors, stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM]);

val rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_CURRENT_BD_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_CURRENT_BD_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_STATE_WRITE_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_CURRENT_BD_PA_def] THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_PACKET_ERROR_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  MATCH_MP_TAC rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_CURRENT_BD_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``mr' : memory_request option`` THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_NEXT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_PACKET_ERROR_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NEXT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_PACKET_ERROR_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic' \/
    RX_STATE_WRITE_PACKET_ERROR nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  Cases_on `RX_STORE_MORE_BYTES nic.rx` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_PACKET_ERROR_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rx_2issue_next_memory_write_request_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_STORE_MORE_BYTES nic.rx /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_STRUCTURE_SAME_STATE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_NOT_RX_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_NOT_RX_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    ~RX_STORE_MORE_BYTES nic.rx /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_STRUCTURE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);



(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic mr' nic'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
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
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NEXT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_PACKET_ERROR_lemma)) THEN
  Cases_on `RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'` THENL
  [
   MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   MATCH_MP_TAC RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
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
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NEXT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_PACKET_ERROR_lemma)) THEN
  Cases_on `RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'` THENL
  [
   MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   MATCH_MP_TAC RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``FST o rx_2issue_next_memory_write_request`` THEN
  ASM_REWRITE_TAC [RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma] THEN
  MATCH_MP_TAC rx_2issue_next_memory_write_request_FST_lemma THEN
  EXISTS_TAC ``mr' : memory_request option`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_2issue_next_memory_write_request_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NEXT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_PACKET_ERROR_lemma)) THEN
  Cases_on `RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'` THENL
  [
   MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   MATCH_MP_TAC RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
   ASM_REWRITE_TAC []
  ]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

val rx_2issue_next_memory_write_request_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_STORE_MORE_BYTES nic.rx
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_RX_STORE_MORE_BYTES_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  MATCH_MP_TAC RX_UNSEEN_BD_QUEUE_DEP_lemma THEN
  RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def THEN
  RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_STORE_MORE_BYTES_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_STORE_MORE_BYTES_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

(*The case ~RX_STORE_MORE_BYTES*)

val rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_RX_STORE_MORE_BYTES_NEXT_STATE_WRITE_PACKET_ERROR_lemma)) THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_CURRENT_BD_NDP_EQ_CPPI_RAM_EQ_IMP_RX_UNSEEN_BD_QUEUE_EQ_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` RX_STATE_WRITE_PACKET_ERROR_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_SUBINVARIANT_IMP_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

(************************************************)
(**Start of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(************************************************)

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (FST o rx_2issue_next_memory_write_request) nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  Cases_on `RX_STORE_MORE_BYTES nic.rx` THENL
  [
   MATCH_MP_TAC rx_2issue_next_memory_write_request_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma THEN
   EXISTS_TAC ``(SND o rx_2issue_next_memory_write_request) nic`` THEN
   REWRITE_TAC [combinTheory.o_DEF] THEN
   BETA_TAC THEN
   ASM_REWRITE_TAC [pairTheory.PAIR]
   ,
   MATCH_MP_TAC rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_IMP_EQ_UNSEEN_BD_QUEUE_lemma THEN
   EXISTS_TAC ``(SND o rx_2issue_next_memory_write_request) nic`` THEN
   REWRITE_TAC [combinTheory.o_DEF] THEN
   BETA_TAC THEN
   ASM_REWRITE_TAC [pairTheory.PAIR]
  ]);

val rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas_def = Define `
  rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (FST o rx_2issue_next_memory_write_request) 
    nic
    rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [NIC_DELTA_PRESERVES_CPPI_RAM_def] (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_CPPI_RAM_lemma)]);

val rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma = store_thm (
  "rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma",
  ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas
    (MAP SND rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas)``,
  REWRITE_TAC [rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val rx_2issue_next_memory_write_request_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (FST o rx_2issue_next_memory_write_request)
    nic
    rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas
    (MAP SND rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_2issue_next_memory_write_request_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic. BD_PAs_IN_RX_SEEN_BD_QUEUE (MAP SND rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas) nic``,
  GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [EMPTY_IN_RX_SEEN_BD_QUEUE_lemma]);

val rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    (FST o rx_2issue_next_memory_write_request)
    nic
    rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_IN_RX_SEEN_BD_QUEUE_lemma]);

(**********************************************)
(**End of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(**********************************************)

(*******************************************************************************)
(**Start of Lemmas for NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES**)
(*******************************************************************************)

val rx_2issue_next_memory_write_request_INCREMENTS_NEXT_BUFFER_BYTE_ADDRESS_lemma = store_thm (
  "rx_2issue_next_memory_write_request_INCREMENTS_NEXT_BUFFER_BYTE_ADDRESS_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    (nic'.rx.next_buffer_byte_address = nic.rx.next_buffer_byte_address + 1w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_2issue_next_memory_write_request_INCREMENTS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma = store_thm (
  "rx_2issue_next_memory_write_request_INCREMENTS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    (nic'.rx.current_bd_number_of_stored_bytes = nic.rx.current_bd_number_of_stored_bytes + 1w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_2issue_next_memory_write_request_PRESERVES_RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic
    ==>
    RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_INCREMENTS_NEXT_BUFFER_BYTE_ADDRESS_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_INCREMENTS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [wordsTheory.WORD_ADD_ASSOC]);
    
(*****************************************************************************)
(**End of Lemmas for NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES**)
(*****************************************************************************)

(******************************************************)
(**Start of Lemmas for NEXT_MEMORY_WRITE_PA_IN_BUFFER**)
(******************************************************)

(* Proof of:
   pa = base + offset /\
   base <=+ pa /\
   pa <=+ base + (size - 1w) /\
   offset <+ size - 1w
   ==>
   base <=+ pa + 1w /\
   pa + 1 <=+ base + (size - 1w) *)

val Lemma1 = blastLib.BBLAST_PROVE
  ``!base offset offset_end : 32 word.
    base + offset <=+ base + offset_end /\
    offset <+ offset_end
    ==>
    base + offset <+ base + offset_end``;

val Lemma2 = blastLib.BBLAST_PROVE ``!x : 32 word y. x <+ y ==> x <+ x + 1w``;

(* Depends on Lemma 1 and 2. *)
val Lemma3 = prove (
  ``!base : 32 word offset size.
    base + offset <=+ base + (size - 1w) /\
    offset <+ size - 1w
    ==>
    base + offset <+ (base + offset) + 1w``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC Lemma2 THEN
  EXISTS_TAC ``base + (size - 1w : 32 word)`` THEN
  MATCH_MP_TAC Lemma1 THEN
  ASM_REWRITE_TAC []);

val Lemma4 = prove (
  ``!base offset : 32 word.
    base <=+ base + offset /\
    base + offset <+ (base + offset) + 1w
    ==>
    base <=+ (base + offset) + 1w``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC wordsTheory.WORD_LOWER_IMP_LOWER_OR_EQ THEN
  MATCH_MP_TAC wordsTheory.WORD_LOWER_EQ_LOWER_TRANS THEN
  EXISTS_TAC ``base + offset : 32 word`` THEN
  ASM_REWRITE_TAC []);

val Lemma5 = blastLib.BBLAST_PROVE ``!x y : 32 word. x <+ y ==> x + 1w <=+ y``;

(* Depends on Lemmas 1 - 4. *)
val Lemma6 = prove (
  ``!base offset size : 32 word.
    base <=+ base + offset /\
    base + offset <=+ base + (size - 1w) /\
    offset <+ size - 1w
    ==>
    base <=+ (base + offset) + 1w``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC Lemma4 THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC Lemma3 THEN
  EXISTS_TAC ``size : 32 word`` THEN
  ASM_REWRITE_TAC []);

(* Depends on Lemmas 1 and 5. *)
val Lemma7 = prove (
  ``!base offset size : 32 word.
    base + offset <=+ base + (size - 1w) /\
    offset <+ size - 1w
    ==>
    (base + offset) + 1w <=+ base + (size - 1w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC Lemma5 THEN
  MATCH_MP_TAC Lemma1 THEN
  ASM_REWRITE_TAC []);

(* Depends on Lemmas 1 through 7. *)
val Lemma8 = prove (
  ``!base offset size : 32 word.
    base <=+ base + offset /\
    base + offset <=+ base + (size - 1w) /\
    offset <+ size - 1w
    ==>
    base <=+ (base + offset) + 1w /\
    (base + offset) + 1w <=+ base + (size - 1w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  CONJ_TAC THENL
  [
   MATCH_MP_TAC Lemma6 THEN
   EXISTS_TAC ``size : 32 word`` THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC Lemma7 THEN
   ASM_REWRITE_TAC []
  ]);

(* Depends on Lemmas 1-8. *)
val Lemma9 = prove (
  ``!pa base offset size : 32 word.
    (pa = base + offset) /\
    offset <+ (size - 1w) /\
    base <=+ pa /\
    pa <=+ base + (size - 1w)
    ==>
    base <=+ pa + 1w /\
    pa + 1w <=+ base + (size - 1w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC Lemma8 THEN
  SPLIT_ASM_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``pa = base + offset`` ``base <=+ pa`` THEN
  ASM_RW_ASM_TAC ``pa = base + offset`` ``pa <=+ base + (size - 1w)`` THEN
  ASM_REWRITE_TAC []);

val Lemma10 = prove (
  ``!nic.
    (nic.rx.next_buffer_byte_address = nic.rx.current_bd.bp + nic.rx.current_bd_number_of_stored_bytes) /\
    nic.rx.current_bd_number_of_stored_bytes <+ nic.rx.current_bd_size − 1w /\
    nic.rx.current_bd.bp <=+ nic.rx.next_buffer_byte_address /\
    nic.rx.next_buffer_byte_address <=+ nic.rx.current_bd.bp + (nic.rx.current_bd_size − 1w)
    ==>
    nic.rx.current_bd.bp <=+ nic.rx.next_buffer_byte_address + 1w /\
    nic.rx.next_buffer_byte_address + 1w <=+ nic.rx.current_bd.bp + (nic.rx.current_bd_size − 1w)``,
  REWRITE_TAC [Lemma9]);

(* End of proof of the implication. *)

val rx_2issue_next_memory_write_request_INCREMENTS_PA_OF_NEXT_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "rx_2issue_next_memory_write_request_INCREMENTS_PA_OF_NEXT_MEMORY_WRITE_REQUEST_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    (nic'.rx.next_buffer_byte_address = nic.rx.next_buffer_byte_address + 1w) /\
    (nic'.rx.current_bd_number_of_stored_bytes = nic.rx.current_bd_number_of_stored_bytes + 1w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn term => true) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors, combinTheory.K_THM]);

val rx_2issue_next_memory_write_request_PRESERVES_RX_NEXT_BUFFER_BYTE_ADDRES_IN_CURRENT_BD_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_RX_NEXT_BUFFER_BYTE_ADDRES_IN_CURRENT_BD_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STORE_MORE_BYTES nic.rx /\
    RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic /\
    RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic
    ==>
    RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``RX_STORE_MORE_BYTES nic`` RX_STORE_MORE_BYTES_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_INCREMENTS_PA_OF_NEXT_MEMORY_WRITE_REQUEST_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC Lemma10 THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic`` RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_def THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic`` RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_def THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_2issue_next_memory_write_request_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_STORE_MORE_BYTES nic.rx /\
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic /\
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def] THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT (PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_RX_NEXT_BUFFER_BYTE_ADDRES_IN_CURRENT_BD_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_NOT_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    ~RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn term => true) THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
  REWRITE_TAC [REWRITE_RULE [DECIDE ``3 < 20``, DECIDE ``2 < 20``] (SPECL [``3 : num``, ``2 : num``] stateTheory.num2rx_abstract_state_11)] THEN
  DECIDE_TAC);

val rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NOT_STORE_MORE_BYTES_PRESERVES_RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    ~RX_STORE_MORE_BYTES nic.rx
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_NOT_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
  ASM_REWRITE_TAC []);

(****************************************************)
(**End of Lemmas for NEXT_MEMORY_WRITE_PA_IN_BUFFER**)
(****************************************************)

(**********************************************************)
(**Start of lemmas for memory requests to writable memory**)
(**********************************************************)

val rx_2issue_next_memory_write_request_RX_MEMORY_SUBINVARIANT_IMP_WRITE_WRITABLE_MEMORY_lemma = store_thm (
  "rx_2issue_next_memory_write_request_RX_MEMORY_SUBINVARIANT_IMP_WRITE_WRITABLE_MEMORY_lemma",
  ``!nic nic' mr' pa WRITABLE.
    ((nic', mr') = rx_2issue_next_memory_write_request nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
    RX_INVARIANT_MEMORY_WRITABLE nic WRITABLE /\
    (pa = (THE mr').pa)
    ==>
    WRITABLE pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  SPLIT_ASM_TAC THEN
  REPEAT (WEAKEN_TAC is_eq) THEN
  REWRITE_TAC [optionTheory.THE_DEF] THEN
  REWRITE_TAC [GSYM stateTheory.memory_request_updates_eq_literal] THEN
  Cases_on `m` THEN
  REWRITE_TAC [stateTheory.memory_request_pa_fupd, stateTheory.memory_request_v_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.memory_request_pa] THEN
  RW_ASM_TAC ``RX_INVARIANT_MEMORY_WRITABLE nic WRITABLE`` RX_INVARIANT_MEMORY_WRITABLE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic WRITABLE`` RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def THEN
  RW_ASM_TAC ``RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic`` RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def THEN
  RW_ASM_TAC ``RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic`` RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` ``P ==> Q`` THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic`` RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``nic.rx.next_buffer_byte_address`` thm))) THEN
  ASM_REWRITE_TAC []);

(*********************************************************)
(**End of lemmas for memory requests to writable memory**)
(*********************************************************)

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas
    (rx_bd_queue nic)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      (FST o rx_2issue_next_memory_write_request)
      nic
      rx_2issue_next_memory_write_request_cppi_ram_write_step_bd_pas
      (rx_bd_queue nic)``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val _ = export_theory();

