open HolKernel Parse boolLib bossLib;
open stateTheory;
open schedulerTheory;
open txTheory;
open register_readTheory;
open register_writeTheory;

val _ = new_theory "nic_model";

val nic_transition_register_read_def = Define `
  nic_transition_register_read (env : environment) (pa : 32 word) (nic : nic_state) =
  read_register env pa nic`;

val nic_transition_register_write_def = Define `
  nic_transition_register_write (env : environment) (pa : 32 word) (value : 32 word) (nic : nic_state) =
  write_register env pa value nic`;

val nic_transition_autonomous_def = Define `
  nic_transition_autonomous (env : environment) (nic : nic_state) =
  scheduler env nic`;

val nic_transition_memory_read_reply_def = Define `
  nic_transition_memory_read_reply (mr : memory_request) (nic : nic_state) =
  tx_3process_memory_read_reply mr nic`

val _ = export_theory();

