open HolKernel Parse boolLib bossLib;
open helperTactics;
open it_transition_definitionsTheory;
open schedulerTheory;
open itTheory;
open it_state_definitionsTheory;
open nic_rw_tactics;
open tx_transition_definitionsTheory;
open rx_transition_definitionsTheory;
open tx_state_definitionsTheory;

val _ = new_theory "it_transition_lemmas";

val IT_AUTONOMOUS_TRANSITION_IMP_NEXT_EQ_it_1reset_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NEXT_EQ_it_1reset_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    (nic' = it_1reset nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [IT_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [IT_ENABLE_def] THEN
  REWRITE_TAC [it_transition_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``nic.it.state = it_reset`` ``nic' = if c then a else b`` THEN
  ASM_REWRITE_TAC []);

val IT_AUTONOMOUS_TRANSITION_IMP_IT_STATE_RESET_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_IT_STATE_RESET_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    IT_STATE_RESET nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [IT_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [IT_ENABLE_def] THEN
  REWRITE_TAC [IT_STATE_RESET_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val IT_AUTONOMOUS_TRANSITION_IMP_NOT_IT_STATE_INITIALIZED_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NOT_IT_STATE_INITIALIZED_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    ~IT_STATE_INITIALIZED nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_IT_STATE_RESET_lemma)) THEN
  RW_ASM_TAC ``IT_STATE_RESET nic`` IT_STATE_RESET_def THEN
  ASM_REWRITE_TAC [IT_STATE_INITIALIZED_def] THEN
  REWRITE_TAC [stateTheory.it_abstract_state_distinct]);

val it_1reset_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma = store_thm (
  "it_1reset_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma",
  ``!nic nic'.
    (nic' = it_1reset nic)
    ==>
    IT_STATE_INITIALIZE_HDP_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [IT_STATE_INITIALIZE_HDP_CP_def] THEN
  REWRITE_TAC [it_1reset_def] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic `i` [stateTheory.it_state_fn_updates, combinTheory.K_THM, stateTheory.it_state_accessors]);

val IT_AUTONOMOUS_TRANSITION_IMP_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    IT_STATE_INITIALIZE_HDP_CP nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC it_1reset_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  MATCH_MP_TAC IT_AUTONOMOUS_TRANSITION_IMP_NEXT_EQ_it_1reset_lemma THEN
  ASM_REWRITE_TAC []);

val IT_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_IT_STATE_RESET_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_IT_STATE_RESET_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    ~IT_STATE_RESET nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma)) THEN
  RW_ASM_TAC ``IT_STATE_INITIALIZE_HDP_CP nic'`` IT_STATE_INITIALIZE_HDP_CP_def THEN
  ASM_REWRITE_TAC [IT_STATE_RESET_def] THEN
  REWRITE_TAC [GSYM stateTheory.it_abstract_state_distinct]);

val IT_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_IT_STATE_INITIALIZED_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_IT_STATE_INITIALIZED_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    ~IT_STATE_INITIALIZED nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma)) THEN
  RW_ASM_TAC ``IT_STATE_INITIALIZE_HDP_CP nic'`` IT_STATE_INITIALIZE_HDP_CP_def THEN
  ASM_REWRITE_TAC [IT_STATE_INITIALIZED_def] THEN
  REWRITE_TAC [stateTheory.it_abstract_state_distinct]);

val IT_AUTONOMOUS_TRANSITION_IMP_IT_TRANSITION_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_IT_TRANSITION_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    (nic' = it_transition nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NEXT_EQ_it_1reset_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_IT_STATE_RESET_lemma)) THEN
  RW_ASM_TAC ``IT_STATE_RESET nic`` IT_STATE_RESET_def THEN
  REWRITE_TAC [it_transition_def] THEN
  ASM_REWRITE_TAC []);

val it_1reset_NON_MODIFICATION_lemma = store_thm (
  "it_1reset_NON_MODIFICATION_lemma",
  ``!nic nic'.
    (nic' = it_1reset nic)
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.it.rx0_hdp_initialized = nic.it.rx0_hdp_initialized) /\
    (nic'.tx = nic.tx) /\
    (nic'.rx = nic.rx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [it_1reset_def] THEN
  rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  rw_state_tactic `i` [stateTheory.it_state_fn_updates, combinTheory.K_THM, stateTheory.it_state_accessors] THEN
  rw_state_tactic `n` [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors]);

val IT_AUTONOMOUS_TRANSITION_NON_MODIFICATION_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_NON_MODIFICATION_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.it.rx0_hdp_initialized = nic.it.rx0_hdp_initialized) /\
    (nic'.tx = nic.tx) /\
    (nic'.rx = nic.rx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC it_1reset_NON_MODIFICATION_lemma THEN
  MATCH_MP_TAC IT_AUTONOMOUS_TRANSITION_IMP_NEXT_EQ_it_1reset_lemma THEN
  ASM_REWRITE_TAC []);

val IT_AUTONOMOUS_TRANSITION_IMP_IT_ENABLE_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_IT_ENABLE_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    IT_ENABLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [IT_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val IT_AUTONOMOUS_TRANSITION_IMP_NOT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NOT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    ~TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_IT_ENABLE_lemma)) THEN
  RW_ASM_TAC ``IT_ENABLE nic`` IT_ENABLE_def THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [TX_ENABLE_def] THEN
  REWRITE_TAC [TX_STATE_PROCESS_MEMORY_READ_REPLY_def] THEN
  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [stateTheory.tx_abstract_state_distinct]);

val IT_AUTONOMOUS_TRANSITION_IMP_NOT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "IT_AUTONOMOUS_TRANSITION_IMP_NOT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic nic'.
    IT_AUTONOMOUS_TRANSITION nic nic'
    ==>
    ~RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_IT_ENABLE_lemma)) THEN
  RW_ASM_TAC ``IT_ENABLE nic`` IT_ENABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RX_ENABLE_def] THEN
  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL IT_AUTONOMOUS_TRANSITION_IMP_NEXT_IT_STATE_INITIALIZE_HDP_CP_lemma)) THEN
  RW_ASM_TAC ``IT_STATE_INITIALIZE_HDP_CP nic'`` IT_STATE_INITIALIZE_HDP_CP_def THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [stateTheory.it_abstract_state_distinct]);
  
val _ = export_theory();

