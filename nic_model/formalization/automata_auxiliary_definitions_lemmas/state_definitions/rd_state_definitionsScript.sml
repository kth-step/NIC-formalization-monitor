open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "rd_state_definitions";

val RD_STATE_IDLE_def = Define `
  RD_STATE_IDLE nic = (nic.rd.state = rd_idle)`;

val RD_STATE_SET_SOP_def = Define `
  RD_STATE_SET_SOP nic = (nic.rd.state = rd_set_sop)`;

val RD_STATE_SET_EOP_def = Define `
  RD_STATE_SET_EOP nic = (nic.rd.state = rd_set_eop)`;

val RD_STATE_SET_EOQ_def = Define `
  RD_STATE_SET_EOQ nic = (nic.rd.state = rd_set_eoq)`;

val RD_STATE_SET_TD_def = Define `
  RD_STATE_SET_TD nic = (nic.rd.state = rd_set_td)`;

val RD_STATE_CLEAR_OWNER_AND_HDP_def = Define `
  RD_STATE_CLEAR_OWNER_AND_HDP nic = (nic.rd.state = rd_clear_owner_and_hdp)`;

val RD_STATE_WRITE_CP_def = Define `
  RD_STATE_WRITE_CP nic = (nic.rd.state = rd_write_cp)`;

val RD_STATE_NOT_IDLE_def = Define `
  RD_STATE_NOT_IDLE nic =
  RD_STATE_SET_SOP nic \/
  RD_STATE_SET_EOP nic \/
  RD_STATE_SET_EOQ nic \/
  RD_STATE_SET_TD nic \/
  RD_STATE_CLEAR_OWNER_AND_HDP nic \/
  RD_STATE_WRITE_CP nic`;

val _ = export_theory();

