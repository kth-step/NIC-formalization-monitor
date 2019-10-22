open HolKernel Parse boolLib bossLib;
open it_state_definitionsTheory;
open rx_state_definitionsTheory;
open tx_state_definitionsTheory;
open rx_transition_definitionsTheory;

val _ = new_theory "itInvariant";

(* If the NIC is in a state where initialization is in progress or has never
   been performed, then the transmission and reception automata are idle. This
   means that during and after completion of initialization, the transmission
   and reception automata cannot perform transitions, and therefore they cannot
   cause the NIC model to enter an undefined state nor issue memory requests to
   disallowed memory regions. That is, the other conjuncts of the NIC invariant
   hold vacously when initialization is complete.

   Depends on: nic.it.state, nic.tx.state, nic.rx.state.

   Preserved by the:
   -initialization automaton: Can only make an autonomous transition from
    it_reset to it_initialize_hdp_cp which means that ~IT_STATE_INITIALIZED is
    true in the pre-state and the post-state. Since the initialization automaton
    does not assign the tx and rx state components, their values are preserved.
   -transmission automaton: ~IT_STATE_INITIALIZED is assumed to be true in the
    post-state. Since the transmission automaton does not assign the nic.it
    state component ~IT_STATE_INITIALIZED is true in the pre-state, which
    implies that TX_STATE_IDLE is true in the pre-state and thereby
    contradicting TX_STATE_AUTONOMOUS_TRANSITION_ENABLE and
    TX_STATE_PROCESS_MEMORY_READ_REPLY. That is, the transmission automaton did
    not perform a transition since the scheduler does not select it when
    TX_STATE_IDLE is false.
   -reception automaton: ~IT_STATE_INITIALIZED is assumed to be true in the
    post-state. Since the reception automaton does not assign the nic.it state
    component ~IT_STATE_INITIALIZED is true in the pre-state, which implies that
    RX_STATE_IDLE is true in the pre-state and thereby contradicting RX_ENABLE.
    That is, the reception automaton did not perform a transition since the
    scheduler does not select it when RX_ENABLE is false.
   -reception teardown automaton: Does not assign the nic.it.state,
    nic.tx.state and nic.rx.state state components and therefore preserves
    IT_NOT_INIT_IMP_TX_RX_RD_IDLE.
   -transmission teardown automaton: Does not assign the nic.it.state,
    nic.tx.state and nic.rx.state state components and therefore preserves
    IT_NOT_INIT_IMP_TX_RX_RD_IDLE. *)
val IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE_def = Define `
  IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE (nic : nic_state) =
  ~IT_STATE_INITIALIZED nic
  ==>
  TX_STATE_IDLE nic /\ RX_STATE_IDLE nic`;

(* If the initialization automaton is resetting itself, then the model variable
   (obesrve model variable and not register) nic.it.rx0_hdp_initialized is false
   (which keeps track of whether RX0_HDP has been initialized or not).

   Depends on: nic.it.state and nic.it.rx0_hdp_initialized.

   Preserved by the:
   -initialization automaton: When the initialization automaton performs an
    autonomous transition, it does so from the state it_reset. The next state is
    it_initialize_hdp_cp. Hence, the invariant is vacously true in the
    post-state due to a contradiction.
   -other automata: The other automata preserve nic.it.state and
    nic.it.rx0_hdp_initialized.
 *)
val RX0_HDP_INITIALIZED_def = Define `
  RX0_HDP_INITIALIZED (nic : nic_state) =
  nic.it.rx0_hdp_initialized`;

val IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT_def = Define `
  IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT (nic : nic_state) =
  IT_STATE_RESET nic
  ==>
  ~RX0_HDP_INITIALIZED nic`;

(* If the initialization automaton is in a state waiting for the CPU to
   initialize the HDP and CP registers, and nic.it.hdp_initialized is true, then
   the reception queue is empty.

   Immedietaly after all HDP and CP registers have been initialized, and the
   initialization automaton enters the state it_initialized, then
   IT_NOT_INIT_IMP_TX_RX_IDLE, IT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY and
   the fact that the initialization automaton only transitions to it_initialized
   when nic.it.rx0_hdp_initialized is true, imply RX_STATE_IDLE and
   RX_BD_QUEUE_EMPTY. RX_STATE_IDLE and RX_BD_QUEUE_EMPTY mean that the reception
   automaton cannot perform an autonomous transition immediately after
   initialization without the CPU writing RX0_HDP. Hence, RX_INVARIANT holds
   vacously after initialization, since RX_STATE_RECEIVE_FRAME is
   false.

   Depends on: nic.it.state, nic.it.rx0_hdp_initialized and nic.rx.sop_bd_pa.

   Preserved by the:
   -initialization automaton: The next state is not it_initialize_hdp_cp when
    the initialization automaton performs an autonomous transition. Hence, the
    invariant is preserved vacously.
   -reception automaton: IT_STATE_INITIALIZE_HDP_CP and RX0_HDP_INITIALIZED hold
    in the post-state, and since the reception automaton does not assign
    nic.it.state nor nic.it.rx0_hdp_initialized, IT_STATE_INITIALIZE_HDP_CP and
    RX0_HDP_INITIALIZED hold in the pre-state. Hence, RX_BD_QUEUE_EMPTY hold in
    the pre-state, meaning that rx_bd_queue nic = [].
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE implies
    MEM nic.rx.current_bd_pa (rx_bd_queue nic) for all states, including
    rx_idle and rx_write cp if ~RX_BD_QUEUE_EMPTY. In all cases a contradiction
    arises.
 *)
val IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY_def = Define `
  IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY (nic : nic_state) =
  IT_STATE_INITIALIZE_HDP_CP nic /\
  RX0_HDP_INITIALIZED nic
  ==>
  RX_BD_QUEUE_EMPTY nic`;

(* The invariant of the initialization automaton. *)
val IT_INVARIANT_def = Define `
  IT_INVARIANT (nic : nic_state) =
  IT_INVARIANT_NOT_INIT_IMP_TX_RX_IDLE nic /\
  IT_INVARIANT_RESET_IMP_NOT_RX_HDP_INIT nic /\
  IT_INVARIANT_RX_HDP_INITIALIZED_IMP_RX_BD_QUEUE_EMPTY nic`;

val _ = export_theory();
