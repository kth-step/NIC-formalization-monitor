open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "td_state_definitions";

val TD_STATE_IDLE_def = Define `
  TD_STATE_IDLE nic = (nic.td.state = td_idle)`;

val TD_STATE_SET_EOQ_def = Define `
  TD_STATE_SET_EOQ nic = (nic.td.state = td_set_eoq)`;

val TD_STATE_SET_TD_def = Define `
  TD_STATE_SET_TD nic = (nic.td.state = td_set_td)`;

val TD_STATE_CLEAR_OWNER_AND_HDP_def = Define `
  TD_STATE_CLEAR_OWNER_AND_HDP nic = (nic.td.state = td_clear_owner_and_hdp)`;

val TD_STATE_WRITE_CP_def = Define `
  TD_STATE_WRITE_CP nic = (nic.td.state = td_write_cp)`;

val TD_STATE_NOT_IDLE_def = Define `
  TD_STATE_NOT_IDLE nic =
  TD_STATE_SET_EOQ nic \/
  TD_STATE_SET_TD nic \/
  TD_STATE_CLEAR_OWNER_AND_HDP nic \/
  TD_STATE_WRITE_CP nic`;

val _ = export_theory();

