open HolKernel Parse boolLib bossLib;
open stateTheory;
open tdInvariantTheory;
open tx_transition_definitionsTheory;

val _ = new_theory "td_invariant_preservation_definitions";

val NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def = Define `
  NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM (nic_delta : nic_delta_type) =
  !nic.
  TD_STATE_WRITE_CPPI_RAM (nic_delta nic)
  ==>
  TD_STATE_WRITE_CPPI_RAM nic`;

val NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_def = Define `
  NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA (nic_delta : nic_delta_type) =
  !nic nic'.
  (nic' = nic_delta nic) /\
  TD_WRITE_CURRENT_BD_PA nic'
  ==>
  NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA nic_delta nic`;

val _ = export_theory();

