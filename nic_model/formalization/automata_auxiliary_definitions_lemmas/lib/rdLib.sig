signature rdLib =
sig

  val rd_transition_defs : Thm.thm list;

  (*
   [``rd_0idle nic``,
    ``rd_1set_sop env nic``,
    ``rd_2set_eop env nic``,
    ``rd_3set_eoq env nic``,
    ``rd_4set_td nic``,
    ``rd_5clear_owner_and_hdp nic``,
    ``rd_6write_cp env nic``] *)
  val rd_transition_function_applications : Term.term list;

  (* Given an id of a reception tear down automaton state, returns the term of
     the return value in terms of the transition function applied in that state.
     For instance:
     0 |-> ``rd_1idle nic``,
     1 |-> ``rx_2set_sop env nic``. *)
  val rd_id_to_rd_transition_function_application : int -> Term.term;

  (* ``rd_0idle nic`` -> 0,
     ``rd_1set_sop env nic`` -> 1. *)
  val rd_transition_function_application_to_rd_id : Term.term -> int;

  (* Given an id of a reception tear down automaton state, returns the term of
     the return value in terms of the transition function applied in that state.
     For instance:
     0 |-> ``rd_0idle nic``,
     1 |-> ``rd_1set_sop env nic``. *)
  val rd_id_to_nic_delta_application : int -> Term.term;

  val RD_STATE_defs : Thm.thm list;

   (* States from which the reception tear down automaton can perform a transition. *)
  val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws : Thm.thm;

  val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_rws : Thm.thm list;

  val RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws : Thm.thm;

  (* Given an id number of a state of the reception tear down automaton, the
     definition of that state is returned, as defined by the list
     RD_STATE_AUTONOMOUS_TRANSTION_ENABLE_CASES_CONJ_defs. *)
  val rd_id_to_rd_transition_state_def : int -> Thm.thm;

  (* The list [``RD_STATE_IDLE nic``,
               ``RD_STATE_FETCH_NEXT_BD nic``,
               ...] *)
  val rd_transition_state_applications : Term.term list;

  (* Given an id number of a state of the reception automaton, the the
     corresponding state definition applied on a term nic is returned. For
     instance: 0 |-> ``RD_STATE_IDLE nic``. *)
  val rd_id_to_rd_transition_state_application : int -> Term.term;

  (* Given a term ``RD_STATE_<name> nic``, returns the correponding rd_id. *)
  val rd_transition_state_application_to_rd_id : Term.term -> int;

  val rd_transition_functions : Term.term list;

  val rd_id_to_rd_transition_function : int -> Term.term;

  val rd_transition_function_to_rd_id : Term.term -> int;

  (* Given a conjunction and an index (counted from zero and less than 7), the
     conjunct with position index is returned. There are 7 states of the
     reception tear down automaton. The intension of this function is to return
     a theorem related to the state of the reception tear down automaton with
     the given index. *)
  val get_rd_conjunct : Thm.thm -> int -> Thm.thm;

end

