structure txLib :> txLib =
struct

  open HolKernel Parse boolLib bossLib;
  open txTheory;
  open tx_state_definitionsTheory;
  open tx_transition_definitionsTheory;

  val tx_transition_defs = [
    tx_1fetch_next_bd_def,
    tx_2issue_next_memory_read_request_def,
    tx_3process_memory_read_reply_def,
    tx_4post_process_def,
    tx_5clear_owner_and_hdp_def,
    tx_6write_cp_def];

  val tx_transition_function_applications = [
    ``tx_1fetch_next_bd nic, NONE : memory_request option``,
    ``tx_2issue_next_memory_read_request nic``,
    ``tx_3process_memory_read_reply mr nic, NONE : memory_request option``,
    ``tx_4post_process nic, NONE : memory_request option``,
    ``tx_5clear_owner_and_hdp nic, NONE : memory_request option``,
    ``tx_6write_cp env nic, NONE : memory_request option``];

  (* Given an id of a transmission automaton state, returns the term of the return
     value in terms of the transition function applied in that state. For instance:
     1 |-> ``tx_1fetch_next_bd nic, NONE : memory_request option``,
     2 |-> ``tx_2issue_next_memory_read_request nic``. *)
  fun tx_id_to_tx_transition_function_application (tx_id : int) = List.nth (tx_transition_function_applications, tx_id - 1);

  (* ``rx_1fetch_next_bd nic`` -> 1,
     ``tx_2issue_next_memory_write_request nic`` -> 2. *)
  fun tx_transition_function_application_to_tx_id (transition_function_application : term) =
    let fun find (transition_function_application : term) (index : int) =
      if index < 1 orelse index > 6 then
        raise Fail "tx_transition_function_application_to_tx_id.find: index out of range."
      else if transition_function_application = ``tx_2issue_next_memory_read_request nic`` then
        2
      else if index = 2 then
        find transition_function_application (index + 1) (* index is 2 and application is not 2, go to 3. *)
      else if (#1 o pairSyntax.dest_pair o tx_id_to_tx_transition_function_application) index = transition_function_application then
        index
      else
        find transition_function_application (index + 1)
    in
      find transition_function_application 1
    end;

  (* Theorems for rewriting. *)
  val TX_STATE_defs = [
    TX_STATE_IDLE_def,
    TX_STATE_FETCH_NEXT_BD_def,
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def,
    TX_STATE_PROCESS_MEMORY_READ_REPLY_def,
    TX_STATE_POST_PROCESS_def,
    TX_STATE_CLEAR_OWNER_AND_HDP_def,
    TX_STATE_WRITE_CP_def];

  val TX_STATE_CONJ_defs = LIST_CONJ TX_STATE_defs;

  (* Given an id number of a state of the transmission automaton, the definition of
     that state is returned, as defined by the list TX_STATE_defs. *)
  fun tx_id_to_tx_transition_state_def (tx_id : int) =
    let val number_of_conjuncts = (length o strip_conj o concl) TX_STATE_CONJ_defs in
    let val defs = CONJ_LIST number_of_conjuncts TX_STATE_CONJ_defs in
      List.nth (defs, tx_id)
    end end;

  (* The list [``TX_STATE_IDLE nic``,
               ``TX_STATE_FETCH_NEXT_BD nic``,
               ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic``,
               ...] *)
  val tx_transition_state_applications =
    let val number_of_conjuncts = (length o strip_conj o concl) TX_STATE_CONJ_defs in
    let val defs = CONJ_LIST number_of_conjuncts TX_STATE_CONJ_defs in
    let val extract_tx_state_application = (#1 o dest_eq o #2 o dest_forall o concl) in
      map extract_tx_state_application defs
    end end end;

  (* Given an id number of a state of the transmission automaton, the the
     corresponding state definition applied on a term nic is returned. For
     instance: 1 |-> ``TX_STATE_FETCH_NEXT_BD nic``. *)
  fun tx_id_to_tx_transition_state_application (tx_id : int) = List.nth (tx_transition_state_applications, tx_id);

  (* Given a term ``TX_STATE_X nic``, returns the correponding tx_id. *)
  fun tx_transition_state_application_to_tx_id (tx_transition_state_application : term) =
    let fun compare_term_head term [] tx_id = raise Fail "tx_transition_state_application_to_tx_id: Argument is not a state predicate from which the transmission automaton can perform a transition."
          | compare_term_head term (hd::tl) tx_id =
              if term = hd then
                tx_id
              else
                compare_term_head term tl (tx_id + 1)
    in
      compare_term_head tx_transition_state_application tx_transition_state_applications 0
    end;

  val tx_transition_functions = [
    ``tx_1fetch_next_bd``,
    ``FST o tx_2issue_next_memory_read_request``,
    ``tx_3process_memory_read_reply mr``,
    ``tx_4post_process``,
    ``tx_5clear_owner_and_hdp``,
    ``tx_6write_cp env``];

  (* 1 -> ``tx_1fetch_next_bd``, 2 -> ``FST o tx_2issue_next_memory_read_request``, ...*)
  fun tx_id_to_tx_transition_function (tx_id : int) =
    if tx_id < 1 orelse tx_id > 6 then
      raise Fail "tx_id_to_tx_transition_function: Argument is not a transition function of the transmission automaton."
    else
      List.nth (tx_transition_functions, tx_id - 1);

  (* ``tx_1fetch_next_bd`` -> 1, ``FST o tx_2issue_next_memory_read_request`` -> 2, ...*)
  fun tx_transition_function_to_tx_id (tx_transition_function : Term.term) =
    let fun find_tx_transition_function_id (tx_transition_function : Term.term) (index : int) =
      if index < 0 orelse index > 6 then
        raise Fail "find_tx_transition_function_index: Argument is not a transition function of the transmission automaton."
      else if List.nth (tx_transition_functions, index) = tx_transition_function then
        index + 1
      else
        find_tx_transition_function_id (tx_transition_function) (index + 1);
    in
      find_tx_transition_function_id tx_transition_function 0
    end;

  (* Given a conjunction and an index (counted from zero and less than 7), the
     conjunct with position index is returned. There are seven states of the
     transmission automaton. The intension of this function is to return a
     theorem related to the state of the transmission automaton with the given
     index. *)
  fun get_tx_conjunct (conjunction : Thm.thm) (index_of_conjunct : int) =
    let val number_of_tx_states = (length o #2 o strip_comb o hd o #2 o strip_comb o concl) stateTheory.datatype_tx_abstract_state
    in
      List.nth (CONJ_LIST number_of_tx_states conjunction, index_of_conjunct)
    end;

  val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws = TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def::TX_STATE_defs;

  val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws = LIST_CONJ TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws;

end
