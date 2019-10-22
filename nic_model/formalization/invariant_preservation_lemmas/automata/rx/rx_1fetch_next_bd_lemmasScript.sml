open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_WELL_DEFINED_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemmasTheory;
open rx_transition_definitionsTheory;
open rx_state_definitionsTheory;
open rxInvariantWellDefinedTheory;
open bd_queueTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT2_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open rxInvariantMemoryWritesTheory;

val _ = new_theory "rx_1fetch_next_bd_lemmas";

val rx_1fetch_next_bd_NOT_MODIFIED_lemma = store_thm (
  "rx_1fetch_next_bd_NOT_MODIFIED_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  Cases_on `~BD_LOCATION_DEFINED nic.rx.current_bd_pa` THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   Cases_on `~RX_BD_WELL_DEFINED (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) (RX_CURRENT_BD_SOP nic.rx) nic.regs.RX_BUFFER_OFFSET` THENL
   [
    ASM_REWRITE_TAC [] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
    ,
    ASM_REWRITE_TAC [] THEN
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_rx_fupd, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.rx_state_accessors]
   ]
  ]);

val rx_1fetch_next_bd_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic. NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA rx_1fetch_next_bd nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  Cases_on `~BD_LOCATION_DEFINED nic.rx.current_bd_pa` THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   Cases_on `~RX_BD_WELL_DEFINED (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) (RX_CURRENT_BD_SOP nic.rx) nic.regs.RX_BUFFER_OFFSET` THENL
   [
    ASM_REWRITE_TAC [] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
    ,
    ASM_REWRITE_TAC [] THEN
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_rx_fupd, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.rx_state_accessors]
   ]
  ]);

val rx_1fetch_next_bd_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic. NIC_DELTA_PRESERVES_RX_SOP_BD_PA rx_1fetch_next_bd nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  Cases_on `~BD_LOCATION_DEFINED nic.rx.current_bd_pa` THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   Cases_on `~RX_BD_WELL_DEFINED (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) (RX_CURRENT_BD_SOP nic.rx) nic.regs.RX_BUFFER_OFFSET` THENL
   [
    ASM_REWRITE_TAC [] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
    ,
    ASM_REWRITE_TAC [] THEN
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_rx_fupd, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.rx_state_accessors]
   ]
  ]);

val rx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma",
  ``!nic. NIC_DELTA_PRESERVES_CPPI_RAM rx_1fetch_next_bd nic``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  Cases_on `~BD_LOCATION_DEFINED nic.rx.current_bd_pa` THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   Cases_on `~RX_BD_WELL_DEFINED (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) (RX_CURRENT_BD_SOP nic.rx) nic.regs.RX_BUFFER_OFFSET` THENL
   [
    ASM_REWRITE_TAC [] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_dead_fupd, stateTheory.nic_state_accessors]
    ,
    ASM_REWRITE_TAC [] THEN
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_rx_fupd, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.rx_state_accessors]
   ]
  ]);

(***********************)
(**Lemmas for NOT DEAD**)
(***********************)

val RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    BD_LOCATION_DEFINED nic.rx.current_bd_pa``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
  MATCH_MP_TAC RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_MEM_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_BD_WELL_DEFINED
      (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM)
      (RX_CURRENT_BD_SOP nic.rx)
      nic.regs.RX_BUFFER_OFFSET``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_IMP_RX_BUFFER_OFFSET_REGISTER_EQ_ZERO_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_INVARIANT_BD_WELL_DEFINED_IMP_RX_BD_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_lemma THEN
  MATCH_MP_TAC RX_MEM_BD_QUEUE_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma THEN
  EXISTS_TAC ``rx_unseen_bd_queue nic`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_PRESERVES_NOT_DEAD_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_NOT_DEAD_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn term => is_eq term) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors]);

(******************************)
(**End of Lemmas for NOT DEAD**)
(******************************)

(******************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE**)
(******************************************)

val RX_STATE_IDLE_INIT_INITIALIZED_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_RX_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_RX_CURRENT_BD_PA_lemma",
  ``!nic.
    (RX_STATE_IDLE nic /\ IT_STATE_INITIALIZED nic \/
     RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_FETCH_NEXT_BD nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_START_FROM_CURRENT_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_RX_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_RX_CURRENT_BD_PA_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_IDLE_INIT_INITIALIZED_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_RX_CURRENT_BD_PA_lemma THEN
  Cases_on `RX_STATE_FETCH_NEXT_BD nic` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic`` RX_STATE_RECEIVE_FRAME_def THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_STATE_FETCH_NEXT_BD_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_STATE_FETCH_NEXT_BD_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma",
  ``!nic nic'.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic' /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.rx.current_bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    (nic.rx.current_bd_pa::(rx_unseen_bd_queue nic') = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_BD_QUEUE_STRUCTURE_SUPPORT_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_RX_CURRENT_BD_PA_lemma)) THEN
  RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def] THEN
  REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_SOP_BD_PA_NEQ_ZERO_OR_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma)) THEN

  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.rx.current_bd_pa``, ``t : 32 word list``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_TL_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``t : 32 word list``, ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN

  REFLECT_ASM_TAC ``bd_queue a m = t`` THEN
  ASM_RW_ASM_TAC ``t = bd_queue a m`` ``BD_QUEUE (h::t) a m`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic.rx.current_bd_pa::bd_queue (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC [listTheory.CONS_11, rx_read_bd_ndp_EQ_read_ndp_lemma]);

val RX_BD_QUEUE_EQ_Q_APPEND_RX_UNSEEN_BD_QUEUE_IMP_RX_BD_QUEUE_EQ_Q_APPEND_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_EQ_Q_APPEND_RX_UNSEEN_BD_QUEUE_IMP_RX_BD_QUEUE_EQ_Q_APPEND_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic' bd_pa.
    (?q. rx_bd_queue nic = q ++ rx_unseen_bd_queue nic) /\
    (rx_unseen_bd_queue nic = bd_pa::rx_unseen_bd_queue nic')
    ==>
    (?q. rx_bd_queue nic = q ++ rx_unseen_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_RW_ASM_TAC ``rx_unseen_bd_queue nic = bd_pa::rx_unseen_bd_queue nic'`` ``rx_bd_queue nic = q ++ rx_unseen_bd_queue nic`` THEN
  ASM_REWRITE_TAC [] THEN
  EXISTS_TAC ``q ++ [bd_pa] : 32 word list`` THEN
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]);

val RX_STATE_FETCH_NEXT_BD_ISSUE_MEMORY_REQUEST_RX_SUBINVARIANT_IMP_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_ISSUE_MEMORY_REQUEST_RX_SUBINVARIANT_IMP_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma",
  ``!nic nic'.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic' /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.rx.current_bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_STATE_FETCH_NEXT_BD_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma)) THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``nic.rx.current_bd_pa::rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic`` THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_BD_QUEUE_EQ_Q_APPEND_RX_UNSEEN_BD_QUEUE_IMP_RX_BD_QUEUE_EQ_Q_APPEND_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic.rx.current_bd_pa`` THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_1fetch_next_bd_def, RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCUTRE_SUPPORT_LOCATION_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
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

val rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_UNMODIFIED_RX_SOP_BD_PA_CPPI_RAM_AND_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_PA_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_UNMODIFIED_RX_SOP_BD_PA_CPPI_RAM_AND_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_PA_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.rx.current_bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_1fetch_next_bd_NOT_MODIFIED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_PRESERVES_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_PRESERVES_BD_QUEUE_STRUCTURE_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_UNMODIFIED_RX_SOP_BD_PA_CPPI_RAM_AND_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_PA_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_ISSUE_MEMORY_REQUEST_RX_SUBINVARIANT_IMP_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma)) THEN
  ASM_REWRITE_TAC []);

(****************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE**)
(****************************************)



(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_1fetch_next_bd_INITIALIZES_CURRENT_BD_NDP_lemma = store_thm (
  "rx_1fetch_next_bd_INITIALIZES_CURRENT_BD_NDP_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd.ndp = read_ndp nic'.rx.current_bd_pa nic'.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_1fetch_next_bd_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCUTRE_SUPPORT_LOCATION_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [rx_bd_queueTheory.rx_read_bd_ndp_EQ_read_ndp_lemma]);

val rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPEC_ALL rx_1fetch_next_bd_INITIALIZES_CURRENT_BD_NDP_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_1fetch_next_bd_IDLE_OR_FETCH_NEXT_BD_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "rx_1fetch_next_bd_IDLE_OR_FETCH_NEXT_BD_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCUTRE_SUPPORT_LOCATION_DEFINED_IMP_CURRENT_BD_PA_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.rx_state_accessors]);

val rx_1fetch_next_bd_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "rx_1fetch_next_bd_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_IDLE_OR_FETCH_NEXT_BD_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
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
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma THEN
  MATCH_MP_TAC rx_1fetch_next_bd_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
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
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma THEN
  MATCH_MP_TAC rx_1fetch_next_bd_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``rx_1fetch_next_bd`` THEN
  ASM_REWRITE_TAC [RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_PRESERVES_CPPI_RAM_lemma]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
  MATCH_MP_TAC rx_1fetch_next_bd_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(*********************************************)
(**Start of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*********************************************)

val rx_1fetch_next_bd_SUBINVARIANT_IMP_UNSEEN_BD_QUEUE_EQ_CURRENT_BD_PA_APPEND_UNSEEN_BD_QUEUE_NEW_STATE_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_UNSEEN_BD_QUEUE_EQ_CURRENT_BD_PA_APPEND_UNSEEN_BD_QUEUE_NEW_STATE_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (rx_unseen_bd_queue nic = [nic.rx.current_bd_pa] ++ rx_unseen_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_IDLE_INIT_INITIALIZED_NOT_BD_QUEUE_EMPTY_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_UNMODIFIED_RX_SOP_BD_PA_CPPI_RAM_AND_CURRENT_BD_EQ_RX_READ_BD_CURRENT_BD_PA_AND_NEXT_STATE_ISSUE_MEMORY_REQUEST_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_STATE_FETCH_NEXT_BD_NEXT_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma)) THEN
  REWRITE_TAC [listTheory.APPEND] THEN
  ASM_REWRITE_TAC []);

(*******************************************)
(**End of Lemmas for BD_QUEUE_WELL_DEFINED**)
(*******************************************)

(************************************************)
(**Start of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(************************************************)

val rx_1fetch_next_bd_SUBINVARIANT_IMP_SHRINKS_UNSEEN_BD_QUEUE_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_SHRINKS_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE rx_1fetch_next_bd nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_def] THEN
  EXISTS_TAC ``[nic.rx.current_bd_pa]`` THEN
  MATCH_MP_TAC rx_1fetch_next_bd_SUBINVARIANT_IMP_UNSEEN_BD_QUEUE_EQ_CURRENT_BD_PA_APPEND_UNSEEN_BD_QUEUE_NEW_STATE_lemma THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def = Define `
  rx_1fetch_next_bd_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val rx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    rx_1fetch_next_bd 
    nic
    rx_1fetch_next_bd_cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``rx_1fetch_next_bd nic``] rx_1fetch_next_bd_NOT_MODIFIED_lemma)]);

val rx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma = store_thm (
  "rx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma",
  ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_1fetch_next_bd_cppi_ram_write_step_bd_pas
    (MAP SND rx_1fetch_next_bd_cppi_ram_write_step_bd_pas)``,
  REWRITE_TAC [rx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val rx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION rx_1fetch_next_bd_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [rx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    rx_1fetch_next_bd
    nic
    rx_1fetch_next_bd_cppi_ram_write_step_bd_pas (MAP SND rx_1fetch_next_bd_cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_1fetch_next_bd_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_1fetch_next_bd_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic. BD_PAs_IN_RX_SEEN_BD_QUEUE (MAP SND rx_1fetch_next_bd_cppi_ram_write_step_bd_pas) nic``,
  GEN_TAC THEN
  REWRITE_TAC [rx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [EMPTY_IN_RX_SEEN_BD_QUEUE_lemma]);

val rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    rx_1fetch_next_bd
    nic
    rx_1fetch_next_bd_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_IN_RX_SEEN_BD_QUEUE_lemma]);

(**********************************************)
(**End of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(**********************************************)


(***********************************************)
(**Start of Lemmas for CURRENT_BUFFER_WRITABLE**)
(***********************************************)

val BD_ADDRESSES_WRITABLE_MEMORY_IMP_WRITABLE_BD_BUFFER_lemma = store_thm (
  "BD_ADDRESSES_WRITABLE_MEMORY_IMP_WRITABLE_BD_BUFFER_lemma",
  ``!bd_pa CPPI_RAM WRITABLE bd.
    BD_ADDRESSES_WRITABLE_MEMORY bd_pa CPPI_RAM WRITABLE /\
    (bd = rx_read_bd bd_pa CPPI_RAM)
    ==>
    !pa.
    bd.bp <=+ pa ∧ pa <=+ bd.bp + (bd.bl − 1w)
    ==>
    WRITABLE pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_ADDRESSES_WRITABLE_MEMORY_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``pa : 32 word`` thm)) THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_RW_ASM_TAC ``x = y`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASM_REWRITE_TAC []);

val BD_IN_MEMORY_WRITABLE_BD_QUEUE_IMP_WRITABLE_BD_BUFFER_lemma = store_thm (
  "BD_IN_MEMORY_WRITABLE_BD_QUEUE_IMP_WRITABLE_BD_BUFFER_lemma",
  ``!q CPPI_RAM WRITABLE bd_pa bd.
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE q CPPI_RAM WRITABLE /\
    MEM bd_pa q /\
    (bd = rx_read_bd bd_pa CPPI_RAM)
    ==>
    !pa.
    bd.bp <=+ pa ∧ pa <=+ bd.bp + (bd.bl − 1w)
    ==>
    WRITABLE pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : 32 word`` thm))) THEN
  MATCH_MP_TAC BD_ADDRESSES_WRITABLE_MEMORY_IMP_WRITABLE_BD_BUFFER_lemma THEN
  EXISTS_TAC ``bd_pa : 32 word`` THEN
  EXISTS_TAC ``CPPI_RAM : cppi_ram_type`` THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_ASSIGNS_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_lemma = store_thm (
  "rx_1fetch_next_bd_ASSIGNS_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM ∧
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_1fetch_next_bd_ASSIGNS_BL_IN_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_SIZE_lemma = store_thm (
  "rx_1fetch_next_bd_ASSIGNS_BL_IN_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_SIZE_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd_size = (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM).bl)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic`` RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [wordsTheory.w2w_0] THEN
  REWRITE_TAC [METIS_PROVE [] ``(if sop then 0w : 32 word else 0w : 32 word) = 0w : 32 word``] THEN
  REWRITE_TAC [wordsTheory.WORD_SUB_RZERO]);

val rx_1fetch_next_bd_IMP_CURRENT_BUFFER_WRITABLE_lemma = store_thm (
  "rx_1fetch_next_bd_IMP_CURRENT_BUFFER_WRITABLE_lemma",
  ``!nic nic' WRITABLE.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE
    ==>    
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_ASSIGNS_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_ASSIGNS_BL_IN_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_SIZE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [] (SPECL [``rx_unseen_bd_queue nic``, ``nic.regs.CPPI_RAM``, ``WRITABLE : bd_pa_type -> bool``, ``nic.rx.current_bd_pa``, ``rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM``] BD_IN_MEMORY_WRITABLE_BD_QUEUE_IMP_WRITABLE_BD_BUFFER_lemma))) THEN
  ASM_REWRITE_TAC []);

(*********************************************)
(**End of Lemmas for CURRENT_BUFFER_WRITABLE**)
(*********************************************)

(*******************************************************************************)
(**Start of Lemmas for NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES**)
(*******************************************************************************)

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.next_buffer_byte_address = nic'.rx.current_bd.bp)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic`` RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [wordsTheory.w2w_0] THEN
  REWRITE_TAC [METIS_PROVE [] ``(if sop then 0w : 32 word else 0w : 32 word) = 0w : 32 word``] THEN
  REWRITE_TAC [wordsTheory.WORD_ADD_0]);

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_CURRENT_BD_NUMBER_OF_STORED_BYTES_EQ_ZERO_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_CURRENT_BD_NUMBER_OF_STORED_BYTES_EQ_ZERO_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd_number_of_stored_bytes = 0w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_CURRENT_BD_NUMBER_OF_STORED_BYTES_EQ_ZERO_lemma)) THEN
  ASM_REWRITE_TAC [wordsTheory.WORD_ADD_0]);

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

(*****************************************************************************)
(**End of Lemmas for NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES**)
(*****************************************************************************)

(******************************************************)
(**Start of Lemmas for NEXT_MEMORY_WRITE_PA_IN_BUFFER**)
(******************************************************)

val OVERFLOW_NOT_EXISTS_EQ_FORALL_NOT_lemma = store_thm (
  "OVERFLOW_NOT_EXISTS_EQ_FORALL_NOT_lemma",
  ``!bd.
    (~?offset. offset <+ bd.bl /\ bd.bp + offset <+ bd.bp)
    =
    (!offset. offset >=+ bd.bl \/ bd.bp + offset >=+ bd.bp)``,
  GEN_TAC THEN
  (fn (asl, con) =>
   let val f_tm = ``\offset. offset <+ bd.bl /\ bd.bp + offset <+ bd.bp`` in
   let val a_tm = ``offset : 32 word`` in
   let val x_tm = ``x : 32 word`` in
   (ONCE_REWRITE_TAC [GSYM (BETA_CONV (mk_comb (f_tm, a_tm)))] THEN
    REWRITE_TAC [SPEC f_tm (INST_TYPE [alpha |-> ``: 32 word``] boolTheory.NOT_EXISTS_THM)] THEN
    ONCE_REWRITE_TAC [GEN_ALPHA_CONV a_tm (mk_forall (x_tm, (mk_neg o mk_comb) (f_tm, x_tm)))]) (asl, con)
   end end end) THEN
  BETA_TAC THEN
  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  REWRITE_TAC [wordsTheory.WORD_NOT_LOWER] THEN
  ONCE_REWRITE_TAC [wordsTheory.WORD_HIGHER_EQ] THEN
  REWRITE_TAC []);

val NOT_RX_BUFFER_OVERFLOW_IMP_BP_LEQ_BP_END_lemma = store_thm (
  "NOT_RX_BUFFER_OVERFLOW_IMP_BP_LEQ_BP_END_lemma",
  ``!bd.
    ~RX_BUFFER_OVERFLOW bd 0w
    ==>
    bd.bp <=+ bd.bp + (bd.bl - 1w)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_BUFFER_OVERFLOW_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  RW_ASM_TAC ``P`` boolTheory.NOT_IMP THEN
  RW_ASM_TAC ``P`` wordsTheory.WORD_SUB_RZERO THEN
  RW_ASM_TAC ``P`` wordsTheory.WORD_ADD_0 THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``~P`` OVERFLOW_NOT_EXISTS_EQ_FORALL_NOT_lemma THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``bd.bl - 1w`` thm)) THEN
  Cases_on `bd.bl − 1w >=+ bd.bl` THENL
  [
   PAT_ASSUM ``x >+ y`` (fn c1 => PAT_ASSUM ``x >=+ y`` (fn c2 => ASSUME_TAC (CONJ c1 c2))) THEN
   RW_ASM_TAC ``P /\ Q`` (blastLib.BBLAST_PROVE ``!x : 32 word. ~(x >+ 0w /\ x - 1w >=+ x)``) THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASM_REWRITE_TAC [GSYM wordsTheory.WORD_HIGHER_EQ]
  ]);

val RX_BD_WELL_DEFINED_IMP_BP_LEQ_BP_END_lemma = store_thm (
  "RX_BD_WELL_DEFINED_IMP_BP_LEQ_BP_END_lemma",
  ``!bd sop.
    RX_BD_WELL_DEFINED bd sop 0w
    ==>
    bd.bp <=+ bd.bp + (bd.bl - 1w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_BD_WELL_DEFINED_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [wordsTheory.w2w_0] THEN
  REWRITE_TAC [METIS_PROVE [] ``(if sop then 0w : 32 word else 0w : 32 word) = 0w : 32 word``] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NOT_RX_BUFFER_OVERFLOW_IMP_BP_LEQ_BP_END_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BP_LEQ_BP_END_lemma = store_thm (
  "RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BP_LEQ_BP_END_lemma",
  ``!nic bd.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
    (bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM)
    ==>
    bd.bp <=+ bd.bp + (bd.bl - 1w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  MATCH_MP_TAC RX_BD_WELL_DEFINED_IMP_BP_LEQ_BP_END_lemma THEN
  EXISTS_TAC ``RX_CURRENT_BD_SOP nic.rx`` THEN
  RW_ASM_TAC ``RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic`` RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def THEN
  ASM_RW_ASM_TAC ``nic.regs.RX_BUFFER_OFFSET = 0w`` ``RX_BD_WELL_DEFINED bd sop reg`` THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_BP_EQ_CURRENT_BD_PA_BP_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_BP_EQ_CURRENT_BD_PA_BP_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd.bp = (rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM).bp)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BD_LOCATION_DEFINED_AT_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_IMP_RX_CURRENT_BD_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => true)) THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  Cases_on `r` THEN
  REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]);

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_BP_LEQ_BP_END_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_BP_LEQ_BP_END_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    nic'.rx.current_bd.bp <=+ nic'.rx.current_bd.bp + (nic'.rx.current_bd_size - 1w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_BP_EQ_CURRENT_BD_PA_BP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_ASSIGNS_BL_IN_CPPI_RAM_AT_CURRENT_BD_PA_TO_CURRENT_BD_SIZE_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_BP_LEQ_BP_END_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_lemma = store_thm (
  "rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_BP_LEQ_BP_END_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_NEXT_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_lemma)) THEN
  PAT_ASSUM ``nic' = rx_1fetch_next_bd nic`` (fn thm => ALL_TAC) THEN
  ASM_REWRITE_TAC [RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_def] THEN
  REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL]);

val rx_1fetch_next_bd_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_1fetch_next_bd_SUBINVARIANT_IMP_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_1fetch_next_bd_RX_STATE_RECEIVE_FRAME_OR_FETCH_NEXT_BD_SUBINVARIANT_IMP_RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def]);

(****************************************************)
(**End of Lemmas for NEXT_MEMORY_WRITE_PA_IN_BUFFER**)
(****************************************************)

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val rx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_1fetch_next_bd_cppi_ram_write_step_bd_pas
    (rx_bd_queue nic)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_1fetch_next_bd_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      rx_1fetch_next_bd
      nic
      rx_1fetch_next_bd_cppi_ram_write_step_bd_pas
      (rx_bd_queue nic)``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_1fetch_next_bd_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val _ = export_theory();
