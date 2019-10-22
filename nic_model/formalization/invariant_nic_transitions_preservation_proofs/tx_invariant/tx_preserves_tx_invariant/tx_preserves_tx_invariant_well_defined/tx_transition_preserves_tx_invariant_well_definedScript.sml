open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_transition_lemmasTheory;
open tx_transition_definitionsTheory;

val _ = new_theory "tx_transition_preserves_tx_invariant_well_defined";

val TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemmas = [
  boolTheory.TRUTH,
  tx_1fetch_next_bdTheory.TX_fetch_next_bd_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma,
  tx_2issue_next_memory_read_requestTheory.TX_issue_next_memory_read_request_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma,
  tx_3process_memory_read_replyTheory.TX_process_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma,
  tx_4post_processTheory.TX_post_process_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma,
  tx_5clear_owner_and_hdpTheory.TX_clear_owner_and_hdp_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma,
  tx_6write_cpTheory.TX_write_cp_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma];

val TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_WELL_DEFINED_CONJ_lemmas =
  LIST_CONJ TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemmas;

(*
 * Proof of that the transition function of the transmission automaton preserves
 * the invariant of the transmission automaton implying that the transmission
 * automaton always is in a well-defined state.
 *)
fun asm_rw_tx_transition_state_prove_tx_well_defined_invariant (tx_id : int) =
  ASSUME_TAC (UNDISCH (SPEC_ALL (txLib.get_tx_conjunct TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas tx_id))) THEN
  ASM_RW_ASM_TAC ``f a1 a2 = x`` ``(nic', mr'') = f a1 a2`` THEN
  RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
  TRY (PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) THEN
  PAT_ASSUM ``x = y`` (fn c1 =>
    PAT_ASSUM (txLib.tx_id_to_tx_transition_state_application tx_id) (fn c2 =>
    PAT_ASSUM ``TX_INVARIANT_WELL_DEFINED nic`` (fn c3 =>
    ASSUME_TAC (CONJ c1 (CONJ c2 c3))))) THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (MATCH_MP (txLib.get_tx_conjunct TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_WELL_DEFINED_CONJ_lemmas tx_id) thm)) THEN
  ASM_REWRITE_TAC [];

val tx_transition_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "tx_transition_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_WELL_DEFINED nic
    ==>
    TX_INVARIANT_WELL_DEFINED nic'``,
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
       asm_rw_tx_transition_state_prove_tx_well_defined_invariant tx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end
    end)) THEN
  asm_rw_tx_transition_state_prove_tx_well_defined_invariant 6);

val tx_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic mr nic'.
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_WELL_DEFINED nic /\
    (nic' = tx_3process_memory_read_reply mr nic)
    ==>
    TX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (txLib.get_tx_conjunct TX_TRANSITION_STEP_PRESERVES_TX_INVARIANT_WELL_DEFINED_CONJ_lemmas 3) THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``mr : memory_request`` THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

