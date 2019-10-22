open HolKernel Parse boolLib bossLib;
open nic_modelTheory;
open tx_state_definitionsTheory;

val _ = new_theory "nic_transition_definitions";

val NIC_REGISTER_READ_TRANSITION_def = Define `
  NIC_REGISTER_READ_TRANSITION nic env pa nic' value' =
  ((nic', value') = nic_transition_register_read env pa nic) /\
  WORD32_ALIGNED pa`;

val NIC_AUTONOMOUS_TRANSITION_def = Define`
  NIC_AUTONOMOUS_TRANSITION nic env nic' mr' int' =
  ((nic', mr', int') = nic_transition_autonomous env nic)`;

val NIC_MEMORY_READ_REPLY_TRANSITION_def = Define `
  NIC_MEMORY_READ_REPLY_TRANSITION nic mr nic' =
  (nic' = nic_transition_memory_read_reply mr nic) /\
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic`;

val _ = export_theory();

