open HolKernel Parse boolLib bossLib;
open schedulerTheory;
open txTheory;
open tx_state_definitionsTheory;
open bd_queue_preservation_lemmasTheory;

val _ = new_theory "tx_transition_definitions";

(* The states from which the transmission automaton can perform a transition (if
   in idle with init and not empty bd queue, then reception teardown must be
   idle in order to be able to perform a transition). *)
val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def = Define `
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic = TX_ENABLE nic`;

val TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def = Define `
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic =
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic \/
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic`;

val TX_AUTONOMOUS_TRANSITION_def = Define`
  TX_AUTONOMOUS_TRANSITION nic env nic' mr' =
  ((nic', mr') = tx_transition env nic) /\
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`;

val TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def = Define`
  TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic' =
  (nic' = tx_3process_memory_read_reply mr nic) /\
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic`;





val NIC_DELTA_PRESERVES_TX_SOP_BD_PA_def = Define `
  NIC_DELTA_PRESERVES_TX_SOP_BD_PA (nic_delta : nic_state -> nic_state) (nic : nic_state) =
  ((nic_delta nic).tx.sop_bd_pa = nic.tx.sop_bd_pa)`;

val NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE_def = Define `
  NIC_DELTA_NOT_EXPANDS_TX_BD_QUEUE (nic_delta : nic_delta_type) (nic : nic_state) =
  NIC_DELTA_NOT_EXPANDS_BD_QUEUE nic_delta nic nic.tx.sop_bd_pa (nic_delta nic).tx.sop_bd_pa`;

val NIC_DELTA_CLEARS_TX_SOP_BD_PA_def = Define `
  NIC_DELTA_CLEARS_TX_SOP_BD_PA (nic_delta : nic_delta_type) (nic : nic_state) = 
  ((nic_delta nic).tx.sop_bd_pa = 0w)`;

val NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_def = Define `
  NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA (nic_delta : nic_delta_type) (nic : nic_state) =
  ((nic_delta nic).tx.sop_bd_pa = nic.tx.current_bd.ndp)`;

val NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA_def = Define `
  NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA nic_delta nic =
  NIC_DELTA_PRESERVES_TX_SOP_BD_PA nic_delta nic \/
  NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_TX_SOP_BD_PA nic_delta nic`;

val NIC_DELTA_PRESERVES_TX_STATE_def = Define `
  NIC_DELTA_PRESERVES_TX_STATE (nic_delta : nic_delta_type) =
  !nic. (nic_delta nic).tx.state = nic.tx.state`;

val NIC_DELTA_PRESERVES_TX_def = Define `
  NIC_DELTA_PRESERVES_TX (nic_delta : nic_delta_type) =
  !nic. (nic_delta nic).tx = nic.tx`;

val NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA_def = Define `
  NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA nic_delta nic =
  ((nic_delta nic).tx.current_bd_pa = nic.tx.current_bd_pa)`;

val _ = export_theory();

