open HolKernel Parse boolLib bossLib;
open rx_state_definitionsTheory;
open rd_state_definitionsTheory;
open it_state_definitionsTheory;
open schedulerTheory;
open rxTheory;

val _ = new_theory "rx_transition_definitions";

val RX_STATE_RECEIVE_FRAME_def = Define `
  RX_STATE_RECEIVE_FRAME nic =
  RX_STATE_IDLE nic /\
  ~RX_BD_QUEUE_EMPTY nic /\
  RD_STATE_IDLE nic /\
  IT_STATE_INITIALIZED nic`;

(* The states from which the reception automaton can perform a transition (if in
   idle with init and not empty bd queue, then reception teardown must be idle
   in order to be able to perform a transition). *)
val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def = Define `
  RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic = RX_ENABLE nic`;

val RX_AUTONOMOUS_TRANSITION_def = Define`
  RX_AUTONOMOUS_TRANSITION nic env nic' mr' =
  ((nic', mr') = rx_transition env nic) /\
  RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`;

val NIC_DELTA_PRESERVES_RX_def = Define `
  NIC_DELTA_PRESERVES_RX (nic_delta : nic_delta_type) = !nic. (nic_delta nic).rx = nic.rx`;

val _ = export_theory();

