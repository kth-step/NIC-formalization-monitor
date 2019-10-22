signature txLib =
sig

  val tx_transition_defs : Thm.thm list;

  val tx_transition_function_applications : Term.term list;

  val tx_id_to_tx_transition_function_application : int -> Term.term;

  val tx_transition_function_application_to_tx_id : Term.term -> int;

  val tx_id_to_tx_transition_state_def : int -> Thm.thm;

  val TX_STATE_defs : Thm.thm list;

  val TX_STATE_CONJ_defs : Thm.thm;

  val tx_transition_state_applications : Term.term list;

  val tx_id_to_tx_transition_state_application : int -> Term.term;

  val tx_transition_state_application_to_tx_id : Term.term -> int;

  val tx_transition_functions : Term.term list;

  val tx_id_to_tx_transition_function : int -> Term.term;

  val tx_transition_function_to_tx_id : Term.term -> int;

  (* Given a conjunction and an index (counted from zero and less than 7), the
     conjunct with position index is returned. There are seven states of the
     transmission automaton. The intension of this function is to return a
     theorem related to the state of the transmission automaton with the given
     index. *)
  val get_tx_conjunct : Thm.thm -> int -> Thm.thm;

  val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CONJ_rws : Thm.thm;

end
