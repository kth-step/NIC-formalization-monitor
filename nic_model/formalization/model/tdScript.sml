open HolKernel Parse boolLib bossLib;
open stateTheory;
open CPPI_RAMTheory;
open wordsTheory;

val _ = new_theory "td";

val td_4write_cp_def = Define `
  td_4write_cp (env : environment) (nic : nic_state) =
  nic with <|
    td := nic.td with state := td_idle;
    regs := nic.regs with TX0_CP := 0xFFFFFFFCw;
    tx := nic.tx with interrupt := if env.td.assert_interrupt then T else nic.tx.interrupt;
    interrupt := if env.td.assert_interrupt then T else nic.interrupt
  |>`;

val TD_WRITE_CURRENT_BD_PA_def = Define `
  TD_WRITE_CURRENT_BD_PA (nic : nic_state) = nic.tx.current_bd_pa <> 0w`;

val td_3clear_owner_and_hdp_def = Define `
  td_3clear_owner_and_hdp (nic : nic_state) =
  nic with <|
    td := nic.td with state := td_write_cp;
    regs := nic.regs with <|
      TX0_HDP := 0w;
      CPPI_RAM :=
        if TD_WRITE_CURRENT_BD_PA nic then
          clear_own nic.regs.CPPI_RAM nic.tx.current_bd_pa
        else
          nic.regs.CPPI_RAM
    |>;
    tx := nic.tx with <|
      current_bd_pa := 0w;
      sop_bd_pa := 0w
    |>
  |>`;

val td_2set_td_def = Define `
  td_2set_td (nic : nic_state) =
  if TD_WRITE_CURRENT_BD_PA nic then
    nic with <|
      td := nic.td with state := td_clear_owner_and_hdp;
      regs := nic.regs with CPPI_RAM := set_td nic.regs.CPPI_RAM nic.tx.current_bd_pa
    |>
  else
    td_3clear_owner_and_hdp nic`;

val td_1set_eoq_def = Define `
  td_1set_eoq (env : environment) (nic : nic_state)  =
  if env.td.set_eoq /\ TD_WRITE_CURRENT_BD_PA nic then
    nic with <|
      td := nic.td with state := td_set_td;
      regs := nic.regs with CPPI_RAM := set_eoq nic.regs.CPPI_RAM nic.tx.current_bd_pa
    |>
  else
    td_2set_td nic`;

val td_transition_def = Define `
  td_transition (env : environment) (nic : nic_state) =
  case nic.td.state of
    | td_idle => nic with dead := T
    | td_set_eoq => td_1set_eoq env nic
    | td_set_td => td_2set_td nic
    | td_clear_owner_and_hdp => td_3clear_owner_and_hdp nic
    | td_write_cp => td_4write_cp env nic`;

val _ = export_theory();
