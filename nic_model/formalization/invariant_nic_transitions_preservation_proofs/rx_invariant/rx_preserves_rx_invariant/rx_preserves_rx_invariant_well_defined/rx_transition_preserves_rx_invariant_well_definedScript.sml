open HolKernel Parse boolLib bossLib;
open helperTactics;
open rx_transition_lemmasTheory;
open rx_transition_definitionsTheory;

val _ = new_theory "rx_transition_preserves_rx_invariant_well_defined";

(*
 * Proof of that the function describing the transitions of the reception
 * automaton preserves the invariant of the reception automaton implying that
 * the reception automaton always is in a well-defined state.
 *)

val RX_TRANSITION_STEP_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemmas = [
  rx_0receive_new_frame_preserves_well_definedTheory.rx_0receive_new_frame_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_1fetch_next_bd_preserves_well_definedTheory.rx_1fetch_next_bd_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_2issue_next_memory_write_request_preserves_well_definedTheory.rx_2issue_next_memory_write_request_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_3write_packet_error_preserves_well_definedTheory.rx_3write_packet_error_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_4write_rx_vlan_encap_preserves_well_definedTheory.rx_4write_rx_vlan_encap_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_5write_from_port_preserves_well_definedTheory.rx_5write_from_port_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_6write_eop_buffer_length_preserves_well_definedTheory.rx_6write_eop_buffer_length_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_7set_eop_eop_preserves_well_definedTheory.rx_7set_eop_eop_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_8set_eop_eoq_or_write_sop_buffer_offset_preserves_well_definedTheory.rx_8set_eop_eoq_or_write_sop_buffer_offset_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_9write_sop_buffer_offset_preserves_well_definedTheory.rx_9write_sop_buffer_offset_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_10write_sop_buffer_length_preserves_well_definedTheory.rx_10write_sop_buffer_length_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_11set_sop_sop_preserves_well_definedTheory.rx_11set_sop_sop_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_12write_sop_pass_crc_preserves_well_definedTheory.rx_12write_sop_pass_crc_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_13write_sop_long_preserves_well_definedTheory.rx_13write_sop_long_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_14write_sop_short_preserves_well_definedTheory.rx_14write_sop_short_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_15write_sop_mac_ctl_preserves_well_definedTheory.rx_15write_sop_mac_ctl_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_16write_sop_packet_length_preserves_well_definedTheory.rx_16write_sop_packet_length_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_preserves_well_definedTheory.rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_18clear_sop_owner_and_hdp_preserves_well_definedTheory.rx_18clear_sop_owner_and_hdp_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma,
  rx_19write_cp_preserves_well_definedTheory.rx_19write_cp_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma];

(*
  The following algorithm is used to prove that the reception automaton
  preserves the well-defined invariant:
  1. Find a disjunction among the hypotheses. If no disjunction exists prove the
     goal for write_cp.
  2. Do case analysis on the left disjunct:
     -Case when the nic is in the assumed state: Do necessary rewrites and apply
      the relevant lemma on the state upon case analysis was made to prove the
      goal.
     -Case when the nic is not in the assumed state: Use the negated statement
      and rewrite the disjunction.
  3. Go to 1.
*)
fun asm_rw_rx_transition_state_prove_rx_well_defined_invariant (rx_id : int) =
  ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id))) THEN
  ASM_RW_ASM_TAC ``f a1 a2 = x`` ``(nic', mr'') = f a1 a2`` THEN
  RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
  TRY (PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) THEN
  PAT_ASSUM ``x = y`` (fn c1 =>
    PAT_ASSUM (rxLib.rx_id_to_rx_transition_state_application rx_id) (fn c2 =>
    PAT_ASSUM ``RX_INVARIANT_WELL_DEFINED nic`` (fn c3 =>
    ASSUME_TAC (CONJ c1 (CONJ c2 c3))))) THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (MATCH_MP (List.nth (RX_TRANSITION_STEP_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemmas, rx_id)) thm)) THEN
  ASM_REWRITE_TAC [];

val rx_transition_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma = store_thm (
  "rx_transition_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_WELL_DEFINED nic
    ==>
    RX_INVARIANT_WELL_DEFINED nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_state_lemmasTheory.RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm
    in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id left_disjunct
    in
      ASM_CASES_TAC left_disjunct THENL
      [
       asm_rw_rx_transition_state_prove_rx_well_defined_invariant rx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end
    end)) THEN
  asm_rw_rx_transition_state_prove_rx_well_defined_invariant 19);

val _ = export_theory();

