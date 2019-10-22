structure rdLib :> rdLib =
struct

  open HolKernel Parse boolLib bossLib;
  open rdTheory;
  open rd_state_definitionsTheory;
  open rd_transition_definitionsTheory;
  open schedulerTheory;
  open rx_state_definitionsTheory;

  val rd_transition_defs = [
    rd_0idle_def,
    rd_1set_sop_def,
    rd_2set_eop_def,
    rd_3set_eoq_def,
    rd_4set_td_def,
    rd_5clear_owner_and_hdp_def,
    rd_6write_cp_def];

  (*
   [``rd_0idle nic``,
    ``rd_1set_sop env nic``,
    ``rd_2set_eop env nic``,
    ``rd_3set_eoq env nic``,
    ``rd_4set_td nic``,
    ``rd_5clear_owner_and_hdp nic``,
    ``rd_6write_cp env nic``] *)
  val rd_transition_function_applications =
    let val rd_delta_def_terms = (strip_conj o concl) rd_transition_case_def in
      map (#2 o dest_eq o #2 o strip_forall) rd_delta_def_terms
    end;

  (* Given an id of a reception tear down automaton state, returns the term of
     the return value in terms of the transition function applied in that state.
     For instance:
     0 |-> ``rd_1idle nic``,
     1 |-> ``rd_2set_sop env nic``. *)
  fun rd_id_to_rd_transition_function_application (rd_id : int) = List.nth (rd_transition_function_applications, rd_id);

  (* ``rd_0idle nic`` -> 0,
     ``rd_1set_sop env nic`` -> 1. *)
  fun rd_transition_function_application_to_rd_id (transition_function_application : term) =
    let fun find (transition_function_application : term) (index : int) =
      if index < 0 orelse index > 6 then
        raise Fail "rd_transition_function_application_to_rd_id.find: index out of range."
      else if (#1 o pairSyntax.dest_pair o rd_id_to_rd_transition_function_application) index = transition_function_application then
        index
      else
        find transition_function_application (index + 1)
    in
      find transition_function_application 0
    end;

  (* Given an id of a reception tear down automaton state, returns the term of
     the return value in terms of the transition function applied in that state.
     For instance:
     0 |-> ``rd_0idle nic``,
     1 |-> ``rd_1set_sop env nic``. *)
  fun rd_id_to_nic_delta_application (rd_id : int) =
      (#1 o pairSyntax.dest_pair o List.nth) (rd_transition_function_applications, rd_id);

  val RD_STATE_defs = [
    RD_STATE_IDLE_def,
    RD_STATE_SET_SOP_def,
    RD_STATE_SET_EOP_def,
    RD_STATE_SET_EOQ_def,
    RD_STATE_SET_TD_def,
    RD_STATE_CLEAR_OWNER_AND_HDP_def,
    RD_STATE_WRITE_CP_def];

   (* States from which the reception tear down automaton can perform a transition. *)
  val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws =
    LIST_CONJ RD_STATE_defs;

  val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws = 
    RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def::RX_STATE_IDLE_def::RD_STATE_defs;

  val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws = LIST_CONJ RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws;

  (* Given an id number of a state of the reception tear down automaton, the
     definition of that state is returned, as defined by the list
     RD_STATE_AUTONOMOUS_TRANSTION_ENABLE_CASES_CONJ_defs. *)
  fun rd_id_to_rd_transition_state_def (rd_id : int) =
    let val number_of_conjuncts = (length o strip_conj o concl) RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws in
      List.nth (CONJ_LIST number_of_conjuncts RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws, rd_id)
    end;

  (* The list [``RD_STATE_IDLE nic``,
               ``RD_STATE_FETCH_NEXT_BD nic``,
               ...] *)
  val rd_transition_state_applications =
    let val number_of_conjuncts = (length o strip_conj o concl) RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws in
    let val defs = CONJ_LIST number_of_conjuncts RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws in
    let val extract_rd_transition_state_application = (#1 o dest_eq o #2 o dest_forall o concl) in
      map extract_rd_transition_state_application defs
    end end end;

  (* Given an id number of a state of the reception automaton, the the
     corresponding state definition applied on a term nic is returned. For
     instance: 0 |-> ``RD_STATE_IDLE nic``. *)
  fun rd_id_to_rd_transition_state_application (rd_id : int) = List.nth (rd_transition_state_applications, rd_id);

  (* Given a term ``RD_STATE_<name> nic``, returns the correponding rd_id. *)
  fun rd_transition_state_application_to_rd_id (rd_transition_state_application : term) =
    let fun compare_term_head term [] rd_id = raise Fail "rd_transition_state_application_to_rd_id: Argument is not a state predicate from which the reception tear down automaton can perform a transition."
          | compare_term_head term (hd::tl) rd_id =
              if term = hd then
                rd_id
              else
                compare_term_head term tl (rd_id + 1)
    in
      compare_term_head rd_transition_state_application rd_transition_state_applications 0
    end;

  val rd_transition_functions = map (#1 o strip_comb) rd_transition_function_applications;

  fun rd_id_to_rd_transition_function (rd_id : int) =
    List.nth (rd_transition_functions, rd_id);

  fun rd_transition_function_to_rd_id (rd_transition_function : Term.term) =
    let fun find_rd_transition_function_index (rd_transition_function : Term.term) (index : int) =
      if index < 0 orelse index > 6 then
        raise Fail "find_rd_transition_function_index: Argument is not a transition function of the reception tear down automaton."
      else if List.nth (rd_transition_functions, index) = rd_transition_function then
        index
      else
        find_rd_transition_function_index (rd_transition_function) (index + 1)
    in
      find_rd_transition_function_index rd_transition_function 0
    end;

  (* Given a conjunction and an index (counted from zero and less than 7), the
     conjunct with position index is returned. There are 7 states of the
     reception tear down automaton. The intension of this function is to return
     a theorem related to the state of the reception tear down automaton with
     the given index. *)
  fun get_rd_conjunct (conjunction : Thm.thm) (index_of_conjunct : int) =
    let val number_of_rd_states = (length o #2 o strip_comb o hd o #2 o strip_comb o concl) stateTheory.datatype_rd_abstract_state
    in
      List.nth (CONJ_LIST number_of_rd_states conjunction, index_of_conjunct)
    end;

end
