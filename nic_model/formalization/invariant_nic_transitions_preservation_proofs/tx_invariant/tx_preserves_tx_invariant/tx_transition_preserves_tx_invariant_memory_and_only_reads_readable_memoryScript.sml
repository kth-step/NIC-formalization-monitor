open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_transition_lemmasTheory;
open tx_transition_definitionsTheory;
open txTheory;
open tx_state_definitionsTheory;
open txInvariantTheory;

val _ = new_theory "tx_transition_preserves_tx_invariant_memory_and_only_reads_readable_memory";

val TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_MEMORY_lemmas = [
  boolTheory.TRUTH,
  tx_1fetch_next_bd_memory_readableTheory.TX_fetch_next_bd_PRESERVES_TX_INVARIANT_MEMORY_lemma,
  tx_2issue_next_memory_read_request_memory_readableTheory.TX_issue_next_memory_read_request_PRESERVES_TX_INVARIANT_MEMORY_lemma,
  tx_3process_memory_read_reply_memory_readableTheory.TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma,
  tx_4post_process_memory_readableTheory.TX_post_process_PRESERVES_TX_INVARIANT_MEMORY_lemma,
  tx_5clear_owner_and_hdp_memory_readableTheory.TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_MEMORY_lemma,
  tx_6write_cp_memory_readableTheory.TX_write_cp_PRESERVES_TX_INVARIANT_MEMORY_lemma];

val TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_MEMORY_CONJ_lemmas =
  LIST_CONJ TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_MEMORY_lemmas;

(*
 * Proof of that the transition function of the transmission automaton preserves
 * the complete invariant of the transmission automaton. This invariant implies
 * that the transmission only reads readable memory.
 *)
fun asm_rw_tx_transition_state_prove_tx_memory_invariant (tx_id : int) =
  ASSUME_TAC (UNDISCH (SPEC_ALL (txLib.get_tx_conjunct TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas tx_id))) THEN
  ASM_RW_ASM_TAC ``f a1 a2 = x`` ``(nic', mr') = f a1 a2`` THEN
  RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
  TRY (PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (txLib.get_tx_conjunct TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_MEMORY_CONJ_lemmas tx_id))) THEN
  ASM_REWRITE_TAC [];

val tx_transition_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "tx_transition_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic env nic' mr' READABLE.
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    ((nic', mr') = tx_transition env nic)
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_state_lemmasTheory.TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm
    in
    let val tx_id = txLib.tx_transition_state_application_to_tx_id left_disjunct
    in
      ASM_CASES_TAC left_disjunct THENL
      [
       asm_rw_tx_transition_state_prove_tx_memory_invariant tx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end
    end)) THEN
  asm_rw_tx_transition_state_prove_tx_memory_invariant 6);

val TX_AUTONOMOUS_TRANSITION_PRESERVES_TX_INVARIANT_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_PRESERVES_TX_INVARIANT_lemma",
  ``!nic env nic' mr' READABLE.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT nic READABLE
    ==>
    TX_INVARIANT nic' READABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_TRANSITION_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_PRESERVES_TX_INVARIANT_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

val tx_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic mr nic' READABLE.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (txLib.get_tx_conjunct TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_MEMORY_CONJ_lemmas 3))) THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic mr nic' READABLE.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' /\
    TX_INVARIANT nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_INVARIANT_lemma = store_thm (
  "TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_PRESERVES_TX_INVARIANT_lemma",
  ``!nic mr nic' READABLE.
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' /\
    TX_INVARIANT nic READABLE
    ==>
    TX_INVARIANT nic' READABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_IMP_TX_3PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_memory_read_reply_PRESERVES_TX_INVARIANT_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

(*
 * Proof of that the transition function of the transmission automaton only issues
 * memory read requests to readable memory (specified by the READABLE predicate).
 *)
val tx_transition_ISSUES_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "tx_transition_ISSUES_MEMORY_WRITE_REQUEST_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = tx_transition env nic) /\
    IS_SOME mr'
    ==>
    ((nic', mr') = tx_2issue_next_memory_read_request nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_transition_def] THEN
  Cases_on `nic.tx.state` THEN
  ASM_REWRITE_TAC [stateTheory.tx_abstract_state_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ, boolTheory.AND1_THM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
  RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val tx_transition_ISSUES_MEMORY_WRITE_REQUEST_IMP_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma = store_thm (
  "tx_transition_ISSUES_MEMORY_WRITE_REQUEST_IMP_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = tx_transition env nic) /\
    IS_SOME mr'
    ==>
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def] THEN
  REWRITE_TAC [tx_transition_def] THEN
  Cases_on `nic.tx.state` THEN
  ASM_REWRITE_TAC [stateTheory.tx_abstract_state_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
  RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val TX_transition_ONLY_READS_READABLE_MEMORY_lemma = store_thm (
  "TX_transition_ONLY_READS_READABLE_MEMORY_lemma",
  ``!nic env nic' mr' READABLE.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_MEMORY nic READABLE /\
    IS_SOME mr'
    ==>
    READABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_ISSUES_MEMORY_WRITE_REQUEST_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_transition_ISSUES_MEMORY_WRITE_REQUEST_IMP_TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_2issue_next_memory_read_request_memory_readableTheory.TX_issue_next_memory_read_request_ISSUES_READABLE_PAs_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_AUTONOMOUS_TRANSITION_READS_ONLY_READABLE_MEMORY_lemma = store_thm (
  "TX_AUTONOMOUS_TRANSITION_READS_ONLY_READABLE_MEMORY_lemma",
  ``!nic env nic' mr' READABLE.
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_INVARIANT nic READABLE /\
    IS_SOME mr'
    ==>
    READABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_AUTONOMOUS_TRANSITION_IMP_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  RW_ASM_TAC ``TX_AUTONOMOUS_TRANSITION nic env nic' mr'`` TX_AUTONOMOUS_TRANSITION_def THEN
  RW_ASM_TAC ``TX_INVARIANT nic READABLE`` TX_INVARIANT_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_transition_ONLY_READS_READABLE_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
