open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantTheory;
open rx_transition_definitionsTheory;
open rxInvariantWellDefinedLemmasTheory;
open rxInvariantWellDefinedTheory;

val _ = new_theory "rx_invariant_lemmas";

(****************************************************************************)
(* Start of lemmas about autonomous transitions of the reception automaton. *)
(****************************************************************************)

val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_RX_INVARIANT_IMP_RX_INVARIANT_MEMORY_lemma = store_thm (
  "RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_RX_INVARIANT_IMP_RX_INVARIANT_MEMORY_lemma",
  ``!nic WRITABLE.
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT_MEMORY nic WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_RX_INVARIANT_IMP_RX_INVARIANT_MEMORY_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_RX_INVARIANT_IMP_RX_INVARIANT_MEMORY_lemma",
  ``!nic env nic' mr' WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT_MEMORY nic WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_RX_INVARIANT_IMP_RX_INVARIANT_MEMORY_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma",
  ``!nic env nic' mr' WRITABLE.
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT nic WRITABLE
    ==>
    ~RX_BD_QUEUE_EMPTY nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.RX_ENABLE_def] THEN
  REWRITE_TAC [GSYM rx_state_definitionsTheory.RX_STATE_IDLE_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_state_lemmasTheory.RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_STATE_IDLE_AND_NOT_RX_STATE_WRITE_CP_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``~RX_STATE_IDLE nic`` ``P ==> Q`` THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_WELL_DEFINED_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC []);

(*****************************************************************)
(* End of lemmas about the invariant of the reception automaton. *)
(*****************************************************************)

val _ = export_theory();

