open HolKernel Parse boolLib bossLib;
open helperTactics;
open rx_transition_lemmasTheory;
open tx_state_lemmasTheory;
open tx_transition_lemmasTheory;

val _ = new_theory "rx_transition_preserves_other_automata";

val NIC_DELTA_NOT_MODIFIED_lemmas = [
  rx_0receive_new_frame_lemmasTheory.rx_0receive_new_frame_NOT_MODIFIED_lemma,
  rx_1fetch_next_bd_lemmasTheory.rx_1fetch_next_bd_NOT_MODIFIED_lemma,
  rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_NOT_MODIFIED_lemma,
  rx_3write_packet_error_lemmasTheory.rx_3write_packet_error_NOT_MODIFIED_lemma,
  rx_4write_rx_vlan_encap_lemmasTheory.rx_4write_rx_vlan_encap_NOT_MODIFIED_lemma,
  rx_5write_from_port_lemmasTheory.rx_5write_from_port_NOT_MODIFIED_lemma,
  rx_6write_eop_buffer_length_lemmasTheory.rx_6write_eop_buffer_length_NOT_MODIFIED_lemma,
  rx_7set_eop_eop_lemmasTheory.rx_7set_eop_eop_NOT_MODIFIED_lemma,
  rx_8set_eop_eoq_or_write_sop_buffer_offset_lemmasTheory.rx_8set_eop_eoq_or_write_sop_buffer_offset_NOT_MODIFIED_lemma,
  rx_9write_sop_buffer_offset_lemmasTheory.rx_9write_sop_buffer_offset_NOT_MODIFIED_lemma,
  rx_10write_sop_buffer_length_lemmasTheory.rx_10write_sop_buffer_length_NOT_MODIFIED_lemma,
  rx_11set_sop_sop_lemmasTheory.rx_11set_sop_sop_NOT_MODIFIED_lemma,
  rx_12write_sop_pass_crc_lemmasTheory.rx_12write_sop_pass_crc_NOT_MODIFIED_lemma,
  rx_13write_sop_long_lemmasTheory.rx_13write_sop_long_NOT_MODIFIED_lemma,
  rx_14write_sop_short_lemmasTheory.rx_14write_sop_short_NOT_MODIFIED_lemma,
  rx_15write_sop_mac_ctl_lemmasTheory.rx_15write_sop_mac_ctl_NOT_MODIFIED_lemma,
  rx_16write_sop_packet_length_lemmasTheory.rx_16write_sop_packet_length_NOT_MODIFIED_lemma,
  rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_lemmasTheory.rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_NOT_MODIFIED_lemma,
  rx_18clear_sop_owner_and_hdp_lemmasTheory.rx_18clear_sop_owner_and_hdp_NOT_MODIFIED_lemma,
  rx_19write_cp_lemmasTheory.rx_19write_cp_NOT_MODIFIED_lemma];

val rx_transition_PRESERVES_OTHER_AUTOMATA_lemma = store_thm (
  "rx_transition_PRESERVES_OTHER_AUTOMATA_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic)
    ==>
    (nic'.it = nic.it) /\
    (nic'.tx = nic.tx) /\
    (nic'.td = nic.td) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rxTheory.rx_transition_def] THEN
  Cases_on `nic.rx.state` THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  (let val thm_tactic =
     fn thm =>
       let val nic_delta_application = (#2 o dest_eq o concl) thm in
       let val rx_id = rxLib.rx_transition_function_application_to_rx_id nic_delta_application in
         ASSUME_TAC (MATCH_MP (List.nth (NIC_DELTA_NOT_MODIFIED_lemmas, rx_id)) thm)
       end end
   in
   (PAT_ASSUM ``nic' : nic_state = x`` thm_tactic ORELSE
    PAT_ASSUM ``(nic', mr') = x`` thm_tactic)
   end) THEN
   ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_TRANSITION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_OTHER_AUTOMATA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_EQ_IMP_TX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic' : nic_state``, ``nic : nic_state``] TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_DEP_lemma))) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

