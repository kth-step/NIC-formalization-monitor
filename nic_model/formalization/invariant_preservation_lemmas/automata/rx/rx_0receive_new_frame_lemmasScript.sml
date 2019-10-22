open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open rxTheory;
open rx_bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open rx_state_lemmasTheory;
open it_state_definitionsTheory;
open rx_transition_definitionsTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_lemmasTheory;
open rxInvariantMemoryWritesTheory;
open rx_1fetch_next_bd_lemmasTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT2_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT4_lemmasTheory;
open rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;
open rx_state_definitionsTheory;

val _ = new_theory "rx_0receive_new_frame_lemmas";

val rx_0receive_new_frame_NOT_MODIFIED_lemma = store_thm (
  "rx_0receive_new_frame_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic)
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_0receive_new_frame_def] THEN
  WEAKEN_TAC (fn term => true) THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
   Cases_on `r` THEN
   REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]
   ,
   REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   COND_CASES_TAC THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
   Cases_on `r` THEN
   REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]
  ]);

val rx_0receive_new_frame_PRESERVES_RX_CURRENT_BD_PA_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_RX_CURRENT_BD_PA_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA (rx_0receive_new_frame env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
   Cases_on `r` THEN
   REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors, combinTheory.K_THM]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   COND_CASES_TAC THENL
   [
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors]
    ,
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]
   ]
  ]);

val rx_0receive_new_frame_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_RX_SOP_BD_PA (rx_0receive_new_frame env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
   Cases_on `r` THEN
   REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors, combinTheory.K_THM]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   COND_CASES_TAC THENL
   [
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors]
    ,
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]
   ]
  ]);

val rx_0receive_new_frame_PRESERVES_CPPI_RAM_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_CPPI_RAM_lemma",
  ``!nic env. NIC_DELTA_PRESERVES_CPPI_RAM (rx_0receive_new_frame env) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
   Cases_on `r` THEN
   REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors, combinTheory.K_THM]
   ,
   ASM_REWRITE_TAC [LET_DEF] THEN
   BETA_TAC THEN
   COND_CASES_TAC THENL
   [
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, stateTheory.rx_state_accessors]
    ,
    REPEAT (WEAKEN_TAC (fn term => true)) THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates, stateTheory.nic_state_accessors, combinTheory.K_THM] THEN
    Cases_on `r` THEN
    REWRITE_TAC [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]
   ]
  ]);







val receive_frame_def = Define `
  receive_frame (received_frame : 8 word list) (nic : nic_state) =
  nic with rx := nic.rx with
    <|frame := received_frame;
         frame_length := n2w (LENGTH received_frame);
         frame_bytes_left := n2w (LENGTH received_frame)|>`;

val rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma = store_thm (
  "rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma",
  ``!(nic : nic_state) (env : environment).
    rx_0receive_new_frame env nic = rx_1fetch_next_bd (receive_frame env.rx.received_frame nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_def, receive_frame_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  AP_TERM_TAC THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors]);

val rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma = store_thm (
  "rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic)
    ==>
    ?nic''.
    (nic'' = receive_frame env.rx.received_frame nic) /\
    (nic' = rx_1fetch_next_bd nic'')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  EXISTS_TAC ``receive_frame env.rx.received_frame nic`` THEN
  ASM_REWRITE_TAC [rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma]);

val rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_lemma = store_thm (
  "rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_lemma",
  ``!nic env nic' nic'' nic'''.
    (nic' = rx_0receive_new_frame env nic) /\
    (nic'' = receive_frame env.rx.received_frame nic) /\
    (nic''' = rx_1fetch_next_bd nic'')
    ==>
    (nic' = nic''')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``nic'' = receive_frame env.rx.received_frame nic`` ``nic''' = rx_1fetch_next_bd nic''`` THEN
  ASM_REWRITE_TAC [rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma]);

val receive_frame_NOT_MODIFIED_lemma = store_thm (
  "receive_frame_NOT_MODIFIED_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic)
    ==>
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa) /\
    (nic'.rd.state = nic.rd.state) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.it.state = nic.it.state) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [receive_frame_def] THEN
  Cases_on `nic`  THEN
  REWRITE_TAC [stateTheory.nic_state_accessors, combinTheory.K_THM, stateTheory.nic_state_fn_updates] THEN
  Cases_on `r`  THEN
  REWRITE_TAC [stateTheory.rx_state_accessors, combinTheory.K_THM, stateTheory.rx_state_fn_updates]);

val receive_frame_PRESERVES_RX_STATE_IDLE_lemma = store_thm (
  "receive_frame_PRESERVES_RX_STATE_IDLE_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    RX_STATE_IDLE nic
    ==>
    RX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_INIT_INITIALIZED_lemma = store_thm (
  "receive_frame_PRESERVES_INIT_INITIALIZED_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    IT_STATE_INITIALIZED nic
    ==>
    IT_STATE_INITIALIZED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_STATE_INITIALIZED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma = store_thm (
  "receive_frame_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    ~RX_BD_QUEUE_EMPTY nic
    ==>
    ~RX_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RD_STATE_IDLE_lemma = store_thm (
  "receive_frame_PRESERVES_RD_STATE_IDLE_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    RD_STATE_IDLE nic
    ==>
    RD_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_state_definitionsTheory.RD_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);
    
val receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma = store_thm (
  "receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    RX_STATE_RECEIVE_FRAME nic
    ==>
    RX_STATE_RECEIVE_FRAME nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_RECEIVE_FRAME_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_INIT_INITIALIZED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RD_STATE_IDLE_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_DEP_sop_bd_pa_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_BD_QUEUE_AND_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "receive_frame_PRESERVES_RX_BD_QUEUE_AND_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic)
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic) /\
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_UNSEEN_BD_QUEUE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
   RX_INVARIANT_BD_QUEUE_STRUCTURE nic
   ==>
   RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_PRESERVES_RX_BD_QUEUE_AND_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_UNSEEN_BD_QUEUE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
   RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
   ==>
   RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
   RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
   ==>
   RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_DEP_sop_bd_pa_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
   RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM
   ==>
   RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_UNSEEN_BD_QUEUE_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
   RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
   ==>
   RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_DEP_RX_BUFFER_OFFSET_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_SUBINVARIANT_lemma = store_thm (
  "receive_frame_PRESERVES_RX_SUBINVARIANT_lemma",
  ``!nic env nic'.
    (nic' = receive_frame env.rx.received_frame nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_STATE_RECEIVE_FRAME nic' /\
    RX_INVARIANT_BD_QUEUE_FINITE nic' /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic' /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic' /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic') /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val receive_frame_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "receive_frame_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!nic env nic' WRITABLE.
    (nic' = receive_frame env.rx.received_frame nic) /\
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJUNCT2 (UNDISCH (SPEC_ALL receive_frame_PRESERVES_RX_BD_QUEUE_AND_RX_UNSEEN_BD_QUEUE_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL receive_frame_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);


















(*****************************************************)
(**********START OF NOT DEAD LEMMAS*******************)
(*****************************************************)

val rx_0receive_new_frame_PRESERVES_dead_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_dead_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic'' : nic_state``] receive_frame_PRESERVES_RX_SUBINVARIANT_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPECL [``nic'' : nic_state``, ``nic' : nic_state``] rx_1fetch_next_bd_PRESERVES_NOT_DEAD_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic''`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic : nic_state``, ``env : environment``, ``nic'' : nic_state``] receive_frame_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

(***************************************************)
(**********END OF NOT DEAD LEMMAS*******************)
(***************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(***************************************************)

val rx_0receive_new_frame_INITIALIZES_CURRENT_BD_NDP_lemma = store_thm (
  "rx_0receive_new_frame_INITIALIZES_CURRENT_BD_NDP_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic'.rx.current_bd.ndp = read_ndp nic'.rx.current_bd_pa nic'.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic'' : nic_state``] receive_frame_PRESERVES_RX_SUBINVARIANT_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPECL [``nic'' : nic_state``, ``nic' : nic_state``] rx_1fetch_next_bd_INITIALIZES_CURRENT_BD_NDP_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic''`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma = store_thm (
  "rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT1_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
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
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_0receive_new_frame_INITIALIZES_CURRENT_BD_NDP_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def]);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT1**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(***************************************************)

val rx_0receive_new_frame_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "rx_0receive_new_frame_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_EQ_receive_frame_rx_1fetch_next_bd_TRANS_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``env : environment``, ``nic'' : nic_state``] receive_frame_PRESERVES_RX_SUBINVARIANT_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPECL [``nic'' : nic_state``, ``nic' : nic_state``] rx_1fetch_next_bd_IDLE_OR_FETCH_NEXT_BD_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma) THEN
  ASM_RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic''`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma = store_thm (
  "rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT2_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
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
  MATCH_MP_TAC rx_0receive_new_frame_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT2**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(***************************************************)

val rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma = store_thm (
  "rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
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
  MATCH_MP_TAC rx_0receive_new_frame_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT3**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(***************************************************)

val rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma = store_thm (
  "rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT4_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVES_CURRENT_BD_PA_SOP_BD_PA_CPPI_RAM_BD_QUEUE_STRUCTURE_SUPPORT4_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``(rx_0receive_new_frame env)`` THEN
  REWRITE_TAC [rx_0receive_new_frame_PRESERVES_RX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_PRESERVES_RX_SOP_BD_PA_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_PRESERVES_CPPI_RAM_lemma] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT4**)
(*************************************************)

(***************************************************)
(**Start of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(***************************************************)

val rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "rx_0receive_new_frame_SUBINVARIANT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic) /\
    RX_STATE_RECEIVE_FRAME nic /\
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
  MATCH_MP_TAC rx_0receive_new_frame_NEXT_STATE_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  ASM_REWRITE_TAC []);

(*************************************************)
(**End of Lemmas for BD_QUEUE_STRUCTURE_SUPPORT5**)
(*************************************************)

(************************************************)
(**Start of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(************************************************)

val rx_0receive_new_frame_SUBINVARIANT_IMP_SHRINKS_UNSEEN_BD_QUEUE_lemma = store_thm (
  "rx_0receive_new_frame_SUBINVARIANT_IMP_SHRINKS_UNSEEN_BD_QUEUE_lemma",
  ``!nic env.
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE (rx_0receive_new_frame env) nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_def] THEN
  BETA_TAC THEN
  SUBST_TAC [CONJUNCT2 (GSYM (REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``receive_frame env.rx.received_frame nic``] receive_frame_PRESERVES_RX_BD_QUEUE_AND_RX_UNSEEN_BD_QUEUE_lemma)))] THEN
  REWRITE_TAC [rx_0receive_new_frame_EQ_rx_1fetch_next_bd_receive_frame_lemma] THEN
  EXISTS_TAC ``[(receive_frame env.rx.received_frame nic).rx.current_bd_pa]`` THEN
  MATCH_MP_TAC rx_1fetch_next_bd_SUBINVARIANT_IMP_UNSEEN_BD_QUEUE_EQ_CURRENT_BD_PA_APPEND_UNSEEN_BD_QUEUE_NEW_STATE_lemma THEN
  (fn (asl, con) =>
   let val nic_term = ``nic : nic_state`` in
   let val environment_term = ``env : environment`` in
   let val nic'_term = ``receive_frame env.rx.received_frame nic`` in
   let val specs = SPECL [nic_term, environment_term, nic'_term] in
   let val rw = UNDISCH o (REWRITE_RULE []) in
     (ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_STATE_RECEIVE_FRAME_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_FINITE_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma)) THEN
     ASSUME_TAC (rw (specs receive_frame_PRESERVES_RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemma))) (asl, con)
   end end end end end) THEN
  ASM_REWRITE_TAC []);

val rx_0receive_new_frame_cppi_ram_write_step_bd_pas_def = Define `
  rx_0receive_new_frame_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val rx_0receive_new_frame_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "rx_0receive_new_frame_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (rx_0receive_new_frame env)
    nic
    rx_0receive_new_frame_cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``env : environment``, ``rx_0receive_new_frame env nic``] rx_0receive_new_frame_NOT_MODIFIED_lemma)]);

val rx_0receive_new_frame_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma = store_thm (
  "rx_0receive_new_frame_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma",
  ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_0receive_new_frame_cppi_ram_write_step_bd_pas
    (MAP SND rx_0receive_new_frame_cppi_ram_write_step_bd_pas)``,
  REWRITE_TAC [rx_0receive_new_frame_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val rx_0receive_new_frame_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION rx_0receive_new_frame_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [rx_0receive_new_frame_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rx_0receive_new_frame env)
    nic
    rx_0receive_new_frame_cppi_ram_write_step_bd_pas (MAP SND rx_0receive_new_frame_cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_0receive_new_frame_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_REFL_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val rx_0receive_new_frame_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_0receive_new_frame_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic. BD_PAs_IN_RX_SEEN_BD_QUEUE (MAP SND rx_0receive_new_frame_cppi_ram_write_step_bd_pas) nic``,
  GEN_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [EMPTY_IN_RX_SEEN_BD_QUEUE_lemma]);

val rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE
    (rx_0receive_new_frame env)
    nic
    rx_0receive_new_frame_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_IN_RX_SEEN_BD_QUEUE_lemma]);

(**********************************************)
(**End of Lemmas for MEMORY_WRITABLE_BD_QUEUE**)
(**********************************************)

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val rx_0receive_new_frame_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "rx_0receive_new_frame_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    rx_0receive_new_frame_cppi_ram_write_step_bd_pas
    (rx_bd_queue nic)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_0receive_new_frame_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "rx_0receive_new_frame_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      (rx_0receive_new_frame env)
      nic
      rx_0receive_new_frame_cppi_ram_write_step_bd_pas
      (rx_bd_queue nic)``,
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [rx_0receive_new_frame_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [rx_0receive_new_frame_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside rx_bd_queue nic.**************)
(*****************************************************************)

val _ = export_theory();
