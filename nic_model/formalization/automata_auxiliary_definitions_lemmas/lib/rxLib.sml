structure rxLib :> rxLib =
struct

  open HolKernel Parse boolLib bossLib;
  open rxTheory;
  open rx_state_definitionsTheory;
  open rx_transition_definitionsTheory;
  open it_state_definitionsTheory;
  open schedulerTheory;
  open rd_state_definitionsTheory;

  val rx_transition_defs = [
    rx_0receive_new_frame_def,
    rx_1fetch_next_bd_def,
    rx_2issue_next_memory_write_request_def,
    rx_3write_packet_error_def,
    rx_4write_rx_vlan_encap_def,
    rx_5write_from_port_def,
    rx_6write_eop_buffer_length_def,
    rx_7set_eop_eop_def,
    rx_8set_eop_eoq_or_write_sop_buffer_offset_def,
    rx_9write_sop_buffer_offset_def,
    rx_10write_sop_buffer_length_def,
    rx_11set_sop_sop_def,
    rx_12write_sop_pass_crc_def,
    rx_13write_sop_long_def,
    rx_14write_sop_short_def,
    rx_15write_sop_mac_ctl_def,
    rx_16write_sop_packet_length_def,
    rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def,
    rx_18clear_sop_owner_and_hdp_def,
    rx_19write_cp_def];

  (*val rx_transition_function_applications = map Term [
    `rx_0receive_new_frame env nic, NONE : memory_request option`,
    `rx_1fetch_next_bd nic, NONE : memory_request option`,
    `rx_2issue_next_memory_write_request nic`,
    `rx_3write_packet_error env nic, NONE : memory_request option`,
    `rx_4write_rx_vlan_encap env nic, NONE : memory_request option`,
    `rx_5write_from_port env nic, NONE : memory_request option`,
    `rx_6write_eop_buffer_length nic, NONE : memory_request option`,
    `rx_7set_eop_eop nic, NONE : memory_request option`,
    `rx_8set_eop_eoq_or_write_sop_buffer_offset nic, NONE : memory_request option`,
    `rx_9write_sop_buffer_offset nic, NONE : memory_request option`,
    `rx_10write_sop_buffer_length nic, NONE : memory_request option`,
    `rx_11set_sop_sop nic, NONE : memory_request option`,
    `rx_12write_sop_pass_crc env nic, NONE : memory_request option`,
    `rx_13write_sop_long env nic, NONE : memory_request option`,
    `rx_14write_sop_short env nic, NONE : memory_request option`,
    `rx_15write_sop_mac_ctl env nic, NONE : memory_request option`,
    `rx_16write_sop_packet_length nic, NONE : memory_request option`,
    `rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic, NONE : memory_request option`,
    `rx_18clear_sop_owner_and_hdp nic, NONE : memory_request option`,
    `rx_19write_cp env nic, NONE : memory_request option`];*)
  val rx_transition_function_applications =
    map snd ((#3 o TypeBase.dest_case o #2 o dest_eq o #2 o strip_forall o concl) rx_transition_def);

  (* Given an id of a reception automaton state, returns the term of the return
     value in terms of the transition function applied in that state. For instance:
     1 |-> ``rx_1fetch_next_bd nic, NONE : memory_request option``,
     2 |-> ``rx_2issue_next_memory_write_request nic``. *)
  fun rx_id_to_rx_transition_function_application (rx_id : int) = List.nth (rx_transition_function_applications, rx_id);

  (* ``rx_1fetch_next_bd env nic`` -> 1,
     ``rx_2issue_next_memory_write_request nic`` -> 2. *)
  fun rx_transition_function_application_to_rx_id (transition_function_application : term) =
    let fun find (transition_function_application : term) (index : int) =
      if index < 0 orelse index > 19 then
        raise Fail "rx_transition_function_application_to_rx_id.find: index out of range."
      else if transition_function_application = ``rx_2issue_next_memory_write_request nic`` then
        2
      else if index = 2 then
        find transition_function_application (index + 1) (* index is 2 and application is not 2, go to 3. *)
      else if (#1 o pairSyntax.dest_pair o rx_id_to_rx_transition_function_application) index = transition_function_application then
        index
      else
        find transition_function_application (index + 1)
    in
      find transition_function_application 0
    end;

  (* Given an id of a reception automaton state, returns the term of the return
     value in terms of the transition function applied in that state. For instance:
     1 |-> ``rx_1fetch_next_bd nic``,
     2 |-> ``(FST o rx_2issue_next_memory_write_request) nic``. *)
  fun rx_id_to_nic_delta_application (rx_id : int) =
    if rx_id = 2 then
      ``(FST o rx_2issue_next_memory_write_request) nic``
    else
      (#1 o pairSyntax.dest_pair o List.nth) (rx_transition_function_applications, rx_id);

  val RX_STATE_defs = [
    RX_STATE_IDLE_def,
    RX_STATE_FETCH_NEXT_BD_def,
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def,
    RX_STATE_WRITE_PACKET_ERROR_def,
    RX_STATE_WRITE_RX_VLAN_ENCAP_def,
    RX_STATE_WRITE_FROM_PORT_def,
    RX_STATE_WRITE_EOP_BUFFER_LENGTH_def,
    RX_STATE_SET_EOP_EOP_def,
    RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_def,
    RX_STATE_WRITE_SOP_BUFFER_OFFSET_def,
    RX_STATE_WRITE_SOP_BUFFER_LENGTH_def,
    RX_STATE_SET_SOP_SOP_def,
    RX_STATE_WRITE_SOP_PASS_CRC_def,
    RX_STATE_WRITE_SOP_LONG_def,
    RX_STATE_WRITE_SOP_SHORT_def,
    RX_STATE_WRITE_SOP_MAC_CTL_def,
    RX_STATE_WRITE_SOP_PACKET_LENGTH_def,
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_def,
    RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def,
    RX_STATE_WRITE_CP_def];

   (* States from which the reception automaton can perform a transition. *)
  val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws =
    LIST_CONJ (RX_STATE_RECEIVE_FRAME_def::tl RX_STATE_defs);

  val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws = [
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def,
    RX_ENABLE_def,
    RX_STATE_IDLE_def,
    IT_STATE_INITIALIZED_def,
    RX_BD_QUEUE_EMPTY_def,
    RD_STATE_IDLE_def];

  val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws = LIST_CONJ RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws;

  val RX_STATE_CLASSIFICATION_defs = [
    RX_STATE_WRITE_CURRENT_BD_PA_def,
    RX_STATE_WRITE_EOP_def,
    RX_STATE_WRITE_EOP_SOP_def,
    RX_STATE_WRITE_EOP_OR_EOP_SOP_def,
    RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_def,
    RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def,
    RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA_def,
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_def,
    RX_STATE_WRITE_CPPI_RAM_def,
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def,
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def];

  val RX_STATE_CLASSIFICATION_CONJ_rws = LIST_CONJ RX_STATE_CLASSIFICATION_defs;

  (* Given an id number of a state of the reception automaton, the definition of
     that state is returned, as defined by the list
     RX_STATE_AUTONOMOUS_TRANSTION_ENABLE_CASES_CONJ_rws. *)
  fun rx_id_to_rx_transition_state_def (rx_id : int) =
    let val number_of_conjuncts = (length o strip_conj o concl) RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws in
      List.nth (CONJ_LIST number_of_conjuncts RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws, rx_id)
    end;

  (* The list [``RX_STATE_RECEIVE_FRAME nic``,
               ``RX_STATE_FETCH_NEXT_BD nic``,
               ...] *)
  val rx_transition_state_applications =
    let val number_of_conjuncts = (length o strip_conj o concl) RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws in
    let val defs = CONJ_LIST number_of_conjuncts RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws in
    let val extract_rx_transition_state_application = (#1 o dest_eq o #2 o dest_forall o concl) in
      map extract_rx_transition_state_application defs
    end end end;

  (* Given an id number of a state of the reception automaton, the the
     corresponding state definition applied on a term nic is returned. For
     instance: 1 |-> ``RX_STATE_FETCH_NEXT_BD nic``. *)
  fun rx_id_to_rx_transition_state_application (rx_id : int) = List.nth (rx_transition_state_applications, rx_id);

  (* Given a term ``RX_STATE_X nic``, returns the correponding rx_id. *)
  fun rx_transition_state_application_to_rx_id (rx_transition_state_application : term) =
    let fun compare_term_head term [] rx_id = raise Fail "rx_transition_state_application_to_rx_id: Argument is not a state predicate from which the reception automaton can perform a transition."
          | compare_term_head term (hd::tl) rx_id =
              if term = hd then
                rx_id
              else
                compare_term_head term tl (rx_id + 1)
    in
      compare_term_head rx_transition_state_application rx_transition_state_applications 0
    end;

  val rx_transition_functions = [
    ``rx_0receive_new_frame env``,
    ``rx_1fetch_next_bd``,
    ``FST o rx_2issue_next_memory_write_request``,
    ``rx_3write_packet_error env``,
    ``rx_4write_rx_vlan_encap env``,
    ``rx_5write_from_port env``,
    ``rx_6write_eop_buffer_length``,
    ``rx_7set_eop_eop``,
    ``rx_8set_eop_eoq_or_write_sop_buffer_offset``,
    ``rx_9write_sop_buffer_offset``,
    ``rx_10write_sop_buffer_length``,
    ``rx_11set_sop_sop``,
    ``rx_12write_sop_pass_crc env``,
    ``rx_13write_sop_long env``,
    ``rx_14write_sop_short env``,
    ``rx_15write_sop_mac_ctl env``,
    ``rx_16write_sop_packet_length``,
    ``rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env``,
    ``rx_18clear_sop_owner_and_hdp``,
    ``rx_19write_cp env``];

  fun rx_id_to_rx_transition_function (rx_id : int) =
    List.nth (rx_transition_functions, rx_id);

  fun rx_transition_function_to_rx_id (rx_transition_function : Term.term) =
    let fun find_rx_transition_function_index (rx_transition_function : Term.term) (index : int) =
      if index < 0 orelse index > 19 then
        raise Fail "find_rx_transition_function_index: Argument is not a transition function of the reception automaton."
      else if List.nth (rx_transition_functions, index) = rx_transition_function then
        index
      else
        find_rx_transition_function_index (rx_transition_function) (index + 1)
    in
      find_rx_transition_function_index rx_transition_function 0
    end;

  (* Given a conjunction and an index (counted from zero and less than 20), the
     conjunct with position index is returned. There are 20 states of the
     reception automaton. The intension of this function is to return a theorem
     related to the state of the reception automaton with the given index. *)
  fun get_rx_conjunct (conjunction : Thm.thm) (index_of_conjunct : int) =
    let val number_of_rx_states = (length o #2 o strip_comb o hd o #2 o strip_comb o concl) stateTheory.datatype_rx_abstract_state
    in
      List.nth (CONJ_LIST number_of_rx_states conjunction, index_of_conjunct)
    end;

end
