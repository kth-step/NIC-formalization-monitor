open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_transition_lemmasTheory;
open it_state_lemmasTheory;
open rx_state_lemmasTheory;

val _ = new_theory "tx_transition_preserves_other_automata";

val NIC_DELTA_NOT_MODIFIED_lemmas = [
  boolTheory.TRUTH,
  tx_1fetch_next_bd_lemmasTheory.TX_fetch_next_bd_NON_MODIFICATION_lemma,
  tx_2issue_next_memory_read_request_lemmasTheory.TX_issue_next_memory_read_request_NON_MODIFICATION_lemma,
  tx_3process_memory_read_reply_lemmasTheory.TX_process_memory_read_reply_NON_MODIFICATION_lemma,
  tx_4post_process_lemmasTheory.TX_post_process_NON_MODIFICATION_lemma,
  tx_5clear_owner_and_hdp_lemmasTheory.TX_clear_owner_and_hdp_NON_MODIFICATION_lemma,
  tx_6write_cp_lemmasTheory.TX_write_cp_NON_MODIFICATION_lemma];

val NIC_DELTA_NOT_MODIFIED_CONJ_lemmas = LIST_CONJ NIC_DELTA_NOT_MODIFIED_lemmas;

fun thm_tactic_dead (thm : thm) =
  ASSUME_TAC thm THEN
  ASM_REWRITE_TAC [] THEN
  Cases_on `nic` THEN
  REWRITE_TAC [stateTheory.nic_state_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [stateTheory.nic_state_accessors];

fun thm_tactic_application thm =
  let val nic_delta_application = (#2 o dest_eq o concl) thm in
  let val tx_id = txLib.tx_transition_function_application_to_tx_id nic_delta_application in
    ASSUME_TAC thm THEN
    ASSUME_TAC (MATCH_MP (txLib.get_tx_conjunct NIC_DELTA_NOT_MODIFIED_CONJ_lemmas tx_id) thm) THEN
    ASM_REWRITE_TAC []
  end end;

val tx_transition_PRESERVES_OTHER_AUTOMATA_lemma = store_thm (
  "tx_transition_PRESERVES_OTHER_AUTOMATA_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = tx_transition env nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [txTheory.tx_transition_def] THEN
  Cases_on `nic.tx.state` THEN
  REWRITE_TAC [stateTheory.tx_abstract_state_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  (PAT_ASSUM ``nic' : nic_state = nic with dead := T`` thm_tactic_dead ORELSE
   PAT_ASSUM ``nic' : nic_state = x`` thm_tactic_application ORELSE
   PAT_ASSUM ``(nic', mr') = f a`` thm_tactic_application));

val tx_memory_read_reply_PRESERVES_OTHER_AUTOMATA_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_OTHER_AUTOMATA_lemma",
  ``!nic mr nic'.
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.it = nic.it) /\
    (nic'.td = nic.td) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (txLib.get_tx_conjunct NIC_DELTA_NOT_MODIFIED_CONJ_lemmas 3))) THEN
  ASM_REWRITE_TAC []);

val TX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic' mr'.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'
    ==>
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_TRANSITION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_transition_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma))) THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_REVERSED_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_REVERSED_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic mr nic'.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'
    ==>
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_memory_read_reply_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma))) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

