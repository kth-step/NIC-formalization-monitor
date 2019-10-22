open HolKernel Parse boolLib bossLib;
open helperTactics;
open txTheory;
open tx_transition_definitionsTheory;
open bd_queue_preservation_lemmasTheory;
open tx_state_definitionsTheory;
open txInvariantWellDefinedTheory;
open tx_state_lemmasTheory;
open cppi_ram_writesTheory;
open bd_listTheory;

val _ = new_theory "tx_3process_memory_read_reply_lemmas";

(*
 * The following is a list of which state components that the transmission
 * invariant depends on (nic.dead, nic.tx.sop_bd_pa, nic.regs.CPPI_RAM,
 * nic.tx.current_bd_pa, nic.tx.expects_sop, nic.tx.current_bd), and that the
 * transmission transition functions do not modify:
 *
 * process_memory_read_reply:
 * -nic.dead
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 * -nic.tx.current_bd
 *
 * Since all buffer descriptors are both SOPs and EOPs, no invariant dependent
 * state components are modified. Therefore, nic.tx.current_bd.eop is assumed.
 *)

val TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma = store_thm (
  "TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    nic.tx.current_bd.eop
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.tx.current_bd_pa = nic.tx.current_bd_pa) /\
    (nic'.tx.sop_bd_pa = nic.tx.sop_bd_pa) /\
    (nic'.tx.expects_sop = nic.tx.expects_sop) /\
    (nic'.tx.current_bd.eop = nic.tx.current_bd.eop) /\
    (nic'.tx.current_bd.ndp = nic.tx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_3process_memory_read_reply_def] THEN
  Cases_on `TX_ALL_BYTES_REQUESTED nic.tx` THEN
  Cases_on `¬nic.tx.current_bd.eop` THEN
  (* The following sequence of tactics works for all 4 subgoals. *)  
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  Cases_on `nic` THEN
  Cases_on `nic'` THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  REWRITE_TAC [stateTheory.nic_state_tx_fupd] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_11] THEN
  Cases_on `t` THEN
  Cases_on `t'` THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_11] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val TX_process_memory_read_reply_NON_MODIFICATION_lemma = store_thm (
  "TX_process_memory_read_reply_NON_MODIFICATION_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.tx.sop_bd_pa = nic.tx.sop_bd_pa) /\
    (nic'.tx.current_bd.eop = nic.tx.current_bd.eop) /\
    (nic'.tx.current_bd.ndp = nic.tx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.tx.pa_of_next_memory_buffer_byte = nic.tx.pa_of_next_memory_buffer_byte) /\
    (nic'.tx.number_of_buffer_bytes_left_to_request = nic.tx.number_of_buffer_bytes_left_to_request) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_3process_memory_read_reply_def] THEN
  Cases_on `TX_ALL_BYTES_REQUESTED nic.tx` THENL
  [
   ASM_REWRITE_TAC [] THEN
   Cases_on `¬nic.tx.current_bd.eop` THENL
   [
    ASM_REWRITE_TAC [] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `t` THEN
    REWRITE_TAC [stateTheory.tx_state_accessors] THEN
    REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.tx_state_accessors] THEN
    RW_ASM_TAC ``~P`` stateTheory.nic_state_accessors THEN
    RW_ASM_TAC ``~P`` stateTheory.tx_state_accessors THEN
    ASM_REWRITE_TAC []
    ,
    ASM_REWRITE_TAC [] THEN
    Cases_on `nic` THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.nic_state_accessors] THEN
    Cases_on `t` THEN
    REWRITE_TAC [stateTheory.tx_state_accessors] THEN
    REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
    REWRITE_TAC [combinTheory.K_THM] THEN
    REWRITE_TAC [stateTheory.tx_state_accessors]
   ]
   ,
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_accessors] THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.nic_state_accessors] THEN
   Cases_on `t` THEN
   REWRITE_TAC [stateTheory.tx_state_accessors] THEN
   REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.tx_state_accessors]
  ]);

val tx_3process_memory_read_reply_PRESERVES_TX_SOP_BD_PA_lemma = store_thm (
  "tx_3process_memory_read_reply_PRESERVES_TX_SOP_BD_PA_lemma",
  ``!nic mr. NIC_DELTA_PRESERVES_TX_SOP_BD_PA (tx_3process_memory_read_reply mr) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``mr : memory_request``, ``tx_3process_memory_read_reply mr nic``] TX_process_memory_read_reply_NON_MODIFICATION_lemma)]);

val tx_3process_memory_read_reply_PRESERVES_CPPI_RAM_lemma = store_thm (
  "tx_3process_memory_read_reply_PRESERVES_CPPI_RAM_lemma",
  ``!nic mr. NIC_DELTA_PRESERVES_CPPI_RAM (tx_3process_memory_read_reply mr) nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``mr : memory_request``, ``tx_3process_memory_read_reply mr nic``] TX_process_memory_read_reply_NON_MODIFICATION_lemma)]);



val TX_process_memory_read_reply_ALL_BYTES_REQUESTED_NOT_EOP_IMP_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma = store_thm (
  "TX_process_memory_read_reply_ALL_BYTES_REQUESTED_NOT_EOP_IMP_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_ALL_BYTES_REQUESTED nic.tx /\
    ¬nic.tx.current_bd.eop
    ==>
    ~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_3process_memory_read_reply_def, TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  REWRITE_TAC [stateTheory.tx_abstract_state_distinct]);

val TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma = store_thm (
  "TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma",
  ``!nic.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    nic.tx.current_bd.eop``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_STATE nic`` TX_INVARIANT_CURRENT_BD_STATE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_EOP_STATE nic`` TX_INVARIANT_CURRENT_BD_EOP_STATE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val tx_3process_memory_read_reply_ALL_BYTES_REQUESTED_IMP_NEXT_TX_STATE_POST_PROCESS_lemma = store_thm (
  "tx_3process_memory_read_reply_ALL_BYTES_REQUESTED_IMP_NEXT_TX_STATE_POST_PROCESS_lemma",
  ``!nic mr nic'.
    TX_ALL_BYTES_REQUESTED nic.tx /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_STATE_POST_PROCESS nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_AND_WELL_DEFINED_INVARIANT_IMP_CURRENT_BD_EOP_lemma)) THEN
  ASM_REWRITE_TAC [TX_STATE_POST_PROCESS_def, tx_3process_memory_read_reply_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val tx_3process_memory_read_reply_NOT_ALL_BYTES_REQUESTED_IMP_NEXT_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma = store_thm (
  "tx_3process_memory_read_reply_NOT_ALL_BYTES_REQUESTED_IMP_NEXT_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma",
  ``!nic mr nic'.
    ~TX_ALL_BYTES_REQUESTED nic.tx /\
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def, tx_3process_memory_read_reply_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors]);

val tx_3process_memory_read_reply_TX_INVARIANT_IMP_NEXT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma = store_thm (
  "tx_3process_memory_read_reply_TX_INVARIANT_IMP_NEXT_TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_lemma",
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE_def] THEN
  Cases_on `TX_ALL_BYTES_REQUESTED nic.tx` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_3process_memory_read_reply_ALL_BYTES_REQUESTED_IMP_NEXT_TX_STATE_POST_PROCESS_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_3process_memory_read_reply_NOT_ALL_BYTES_REQUESTED_IMP_NEXT_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val TX_process_memory_read_reply_PRESERVES_CURRENT_BD_EOP_STATE_lemma = store_thm (
  "TX_process_memory_read_reply_PRESERVES_CURRENT_BD_EOP_STATE_lemma",
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_EOP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_STATE nic`` TX_INVARIANT_CURRENT_BD_STATE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_EOP_STATE nic`` TX_INVARIANT_CURRENT_BD_EOP_STATE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_EOP_STATE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_NON_MODIFICATION_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_process_memory_read_reply_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma = store_thm (
  "TX_process_memory_read_reply_PRESERVES_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_lemma",
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_WELL_DEFINED nic`` TX_INVARIANT_WELL_DEFINED_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_STATE nic`` TX_INVARIANT_CURRENT_BD_STATE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic`` TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def THEN
  REWRITE_TAC [BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def] THEN
  DISCH_TAC THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT2 thm)) THEN
  RW_ASM_TAC ``TX_INVARIANT_CURRENT_BD_EOP_STATE nic`` TX_INVARIANT_CURRENT_BD_EOP_STATE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_TX_STATE_NOT_BD_QUEUE_EMPTY_lemma)) THEN
  PAT_ASSUM ``TX_STATE_NOT_BD_QUEUE_EMPTY nic ==> nic.tx.current_bd.eop`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_EOP_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``nic'.tx.current_bd.ndp = nic.tx.current_bd.ndp`` ``nic'.tx.current_bd.ndp <> 0w`` THEN
  RW_ASM_TAC ``P ==> Q`` BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_PROCESS_MEMORY_READ_REPLY nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  RW_ASM_TAC ``CURRENT_BD_NDP_EQ_CPPI_RAM_NDP nic`` CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def THEN
  ASM_REWRITE_TAC [CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def]);






val TX_process_memory_read_reply_ALL_BYTES_REQUESTED_EOP_IMP_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma = store_thm (
  "TX_process_memory_read_reply_ALL_BYTES_REQUESTED_EOP_IMP_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_ALL_BYTES_REQUESTED nic.tx /\
    nic.tx.current_bd.eop
    ==>
    ~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_3process_memory_read_reply_def, TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors] THEN
  Cases_on `t` THEN
  REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.tx_state_accessors] THEN
  REWRITE_TAC [GSYM stateTheory.tx_abstract_state_distinct]);

val TX_process_memory_read_reply_NEXT_STATE_EQ_issue_next_memory_read_request_IMP_BYTES_LEFT_TO_REQUEST_lemma = store_thm (
  "TX_process_memory_read_reply_NEXT_STATE_EQ_issue_next_memory_read_request_IMP_BYTES_LEFT_TO_REQUEST_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'
    ==>
    nic'.tx.number_of_buffer_bytes_left_to_request >+ 0w``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_3process_memory_read_reply_def] THEN
  SPLIT_ASM_TAC THEN
  Cases_on `TX_ALL_BYTES_REQUESTED nic.tx` THENL
  [
   Cases_on `¬nic.tx.current_bd.eop` THENL
   [
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_ALL_BYTES_REQUESTED_NOT_EOP_IMP_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma)) THEN
    ASM_RW_ASM_TAC ``~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'`` ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'`` THEN
    UNDISCH_TAC ``F`` THEN
    ASM_REWRITE_TAC []
    ,
    RW_ASM_TAC ``~~P`` boolTheory.NOT_CLAUSES THEN
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_process_memory_read_reply_ALL_BYTES_REQUESTED_EOP_IMP_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma)) THEN
    ASM_RW_ASM_TAC ``~TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'`` ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic'`` THEN
    UNDISCH_TAC ``F`` THEN
    ASM_REWRITE_TAC []
   ]
   ,
   ASM_REWRITE_TAC [] THEN
   Cases_on `nic` THEN
   REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.nic_state_accessors] THEN
   Cases_on `t` THEN
   REWRITE_TAC [stateTheory.tx_state_fn_updates] THEN
   REWRITE_TAC [combinTheory.K_THM] THEN
   REWRITE_TAC [stateTheory.tx_state_accessors] THEN
   RW_ASM_TAC ``~P`` TX_ALL_BYTES_REQUESTED_def THEN
   RW_ASM_TAC ``~P`` stateTheory.nic_state_accessors THEN
   RW_ASM_TAC ``~P`` stateTheory.tx_state_accessors THEN
   ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``(c5 :32 word) <> 0w ==> c5 >+ 0w``)) THEN
   ASM_REWRITE_TAC []
  ]);

(*****************************************************************)
(**Start of lemmas for showing that the transmission automaton****)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas_def = Define `
  tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas = [] : cppi_ram_write_step_bd_pas_type`;

val tx_3process_memory_read_reply_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "tx_3process_memory_read_reply_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic mr.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
      (tx_3process_memory_read_reply mr)
      nic
      tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  BETA_TAC THEN
  REWRITE_TAC [tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [cppi_ram_write_EMPTY_EQ_ID_lemma] THEN
  REWRITE_TAC [REWRITE_RULE [] (SPECL [``nic : nic_state``, ``mr : memory_request``, ``tx_3process_memory_read_reply mr nic``] TX_process_memory_read_reply_NON_MODIFICATION_lemma)]);

val tx_3process_memory_read_reply_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma = store_thm (
  "tx_3process_memory_read_reply_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma",
  ``!nic.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas
    (tx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM]);

val tx_3process_memory_read_reply_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "tx_3process_memory_read_reply_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
      tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [listTheory.MAP] THEN
  REWRITE_TAC [listTheory.MEM]);

val tx_3process_memory_read_reply_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma = store_thm (
  "tx_3process_memory_read_reply_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma",
  ``!nic mr.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
      (tx_3process_memory_read_reply mr)
      nic
      tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas
      (tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [tx_3process_memory_read_reply_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [tx_3process_memory_read_reply_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_TX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [tx_3process_memory_read_reply_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

val tx_3process_memory_read_reply_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_3process_memory_read_reply_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic q mr.
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM (tx_3process_memory_read_reply mr nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ``tx_3process_memory_read_reply_cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [tx_3process_memory_read_reply_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemma]);

(*****************************************************************)
(**End of lemmas for showing that the transmission automaton******)
(**does not modify CPPI_RAM outside tx_bd_queue nic.**************)
(*****************************************************************)

val _ = export_theory();
