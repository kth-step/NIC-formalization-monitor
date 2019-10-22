open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "it_state_definitions";

val IT_STATE_POWER_ON_def = Define `
  IT_STATE_POWER_ON nic = (nic.it.state = it_power_on)`;

val IT_STATE_RESET_def = Define `
  IT_STATE_RESET nic = (nic.it.state = it_reset)`;

val IT_STATE_INITIALIZE_HDP_CP_def = Define `
  IT_STATE_INITIALIZE_HDP_CP nic = (nic.it.state = it_initialize_hdp_cp)`;

val IT_STATE_INITIALIZED_def = Define `
  IT_STATE_INITIALIZED nic = (nic.it.state = it_initialized)`;

val _ = export_theory();
