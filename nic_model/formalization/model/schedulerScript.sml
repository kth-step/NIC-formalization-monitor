open HolKernel Parse boolLib bossLib;
open stateTheory;
open itTheory;
open txTheory;
open tdTheory;
open rxTheory;
open rdTheory;

val _ = new_theory "scheduler";

val IT_ENABLE_def = Define `
  IT_ENABLE nic =
  (nic.it.state = it_reset) /\
  (nic.tx.state = tx_idle) /\
  (nic.rx.state = rx_idle)`;

val TX_ENABLE_def = Define `
  TX_ENABLE nic =
  nic.tx.state <> tx_idle /\
  nic.tx.state <> tx_process_memory_read_reply`;

val RX_ENABLE_def = Define `
  RX_ENABLE nic =
  ((nic.rx.state = rx_idle) /\ nic.rx.sop_bd_pa <> 0w /\ (nic.rd.state = rd_idle) /\ (nic.it.state = it_initialized)) \/
  nic.rx.state <> rx_idle`;

val TD_ENABLE_def = Define `
  TD_ENABLE nic =
  nic.td.state <> td_idle /\
  (nic.tx.state = tx_idle)`;

val RD_ENABLE_def = Define `
  RD_ENABLE nic =
  nic.rd.state <> rd_idle /\
  (nic.rx.state = rx_idle)`;

val scheduler_case_def = Define `
  (scheduler_case initialize            env nic = (if IT_ENABLE nic then it_transition nic else nic, NONE)) /\
  (scheduler_case transmit              env nic = if TX_ENABLE nic then tx_transition env nic else (nic, NONE)) /\
  (scheduler_case receive               env nic = if RX_ENABLE nic then rx_transition env nic else (nic, NONE)) /\
  (scheduler_case teardown_transmission env nic = (if TD_ENABLE nic then td_transition env nic else nic, NONE)) /\
  (scheduler_case teardown_reception    env nic = (if RD_ENABLE nic then rd_transition env nic else nic, NONE))`;

val scheduler_def = Define `
  scheduler (env : environment) (nic : nic_state) =
    if nic.dead then
      (nic, NONE, nic.interrupt)
    else
      let (nic', mr') = scheduler_case env.scheduler env nic
      in
      (nic', mr', nic'.interrupt)`;

val _ = export_theory();

