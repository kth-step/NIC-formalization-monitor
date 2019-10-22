signature rxLib =
sig

  val rx_transition_defs : Thm.thm list;

(*val rx_transition_function_applications = map Term [
  `rx_0receive_new_frame nic v.received_frame, NONE : memory_request option`,
  `rx_1fetch_next_bd nic, NONE : memory_request option`,
  `rx_2issue_next_memory_write_request nic`,
  `rx_3write_packet_error nic v.packet_error, NONE : memory_request option`,
  `rx_4write_rx_vlan_encap nic v.rx_vlan_encap, NONE : memory_request option`,
  `rx_5write_from_port nic v.from_port, NONE : memory_request option`,
  `rx_6write_eop_buffer_length nic, NONE : memory_request option`,
  `rx_7set_eop_eop nic, NONE : memory_request option`,
  `rx_8set_eop_eoq_or_write_sop_buffer_offset nic, NONE : memory_request option`,
  `rx_9write_sop_buffer_offset nic, NONE : memory_request option`,
  `rx_10write_sop_buffer_length nic, NONE : memory_request option`,
  `rx_11set_sop_sop nic, NONE : memory_request option`,
  `rx_12write_sop_pass_crc nic v.pass_crc, NONE : memory_request option`,
  `rx_13write_sop_long nic v.long, NONE : memory_request option`,
  `rx_14write_sop_short nic v.short, NONE : memory_request option`,
  `rx_15write_sop_mac_ctl nic v.mac_ctl, NONE : memory_request option`,
  `rx_16write_sop_packet_length nic, NONE : memory_request option`,
  `rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp nic v.sop_eop_both_overrun, NONE : memory_request option`,
  `rx_18clear_sop_owner_and_hdp nic, NONE : memory_request option`,
  `rx_19write_cp nic v.assert_interrupt, NONE : memory_request option`];*)
  val rx_transition_function_applications : Term.term list;

  (* Given an id of a reception automaton state, returns the term of the return
     value in terms of the transition function applied in that state. For instance:
     1 |-> ``rx_1fetch_next_bd nic, NONE : memory_request option``,
     2 |-> ``rx_2issue_next_memory_write_request nic``. *)
  val rx_id_to_rx_transition_function_application : int -> Term.term;

  (* ``rx_1fetch_next_bd nic`` -> 1,
     ``rx_2issue_next_memory_write_request nic`` -> 2. *)
  val rx_transition_function_application_to_rx_id : Term.term -> int;

  (* Given an id of a reception automaton state, returns the term of the return
     value in terms of the transition function applied in that state. For instance:
     1 |-> ``rx_1fetch_next_bd nic``,
     2 |-> ``(FST o rx_2issue_next_memory_write_request) nic``. *)
  val rx_id_to_nic_delta_application : int -> Term.term;

  (* Given an id number of a state of the reception automaton, the definition of
     that state is returned, as defined by the list RX_STATE_TRANSTION_defs. *)
  val rx_id_to_rx_transition_state_def : int -> Thm.thm;

  (* The list [``RX_STATE_IDLE_INIT_NOT_BD_QUEUE_EMPTY nic``,
               ``RX_STATE_FETCH_NEXT_BD nic``,
               ...] *)
  val rx_transition_state_applications : Term.term list;

  (* Given an id number of a state of the reception automaton, the the
     corresponding state definition applied on a term nic is returned. For
     instance: 1 |-> ``RX_STATE_FETCH_NEXT_BD nic``. *)
  val rx_id_to_rx_transition_state_application : int -> Term.term;

  (* Given a term ``RX_STATE_X nic``, returns the correponding rx_id. *)
  val rx_transition_state_application_to_rx_id : Term.term -> int;

  (* 0 |-> ``λnic. rx_0receive_new_frame nic received_frame``,
     1 |-> ``rx_1fetch_next_bd``,
     2 |-> ``FST ∘ rx_2issue_next_memory_write_request`` *)
  val rx_id_to_rx_transition_function : int -> Term.term;

  (* Inverse of rx_id_to_rx_transition_function. *)
  val rx_transition_function_to_rx_id : Term.term -> int;

  (* [RX_STATE_IDLE_def, RX_STATE_FETCH_NEXT_BD_def, ...] *)
  val RX_STATE_defs : Thm.thm list;

  (* Rewrites of all states from which the reception automaton can perform a
     transition, in conjunction form. *)
  val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws : Thm.thm;

  (* Rewrites for proofs involving RX_STATE_AUTONOMOUS_TRANSITION_ENABLE. *)
  val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws : Thm.thm list;

  (* The rewrites used in proofs involving RX_STATE_AUTONOMOUS_TRANSITION_ENABLE but in
     the form of a conjunction. *)
  val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws : Thm.thm;

  (* Rewrites regarding classification of states. *)
  val RX_STATE_CLASSIFICATION_defs : Thm.thm list;

  (* Rewrites regarding classification of states but in the form of a conjunction. *)
  val RX_STATE_CLASSIFICATION_CONJ_rws : Thm.thm;

  (* Given a conjunction and an index (counted from zero and less than 20), the
     conjunct with position index is returned. There are 20 states of the
     reception automaton. The intension of this function is to return a theorem
     related to the state of the reception automaton with the given index. *)
  val get_rx_conjunct : Thm.thm -> int -> Thm.thm;

end

