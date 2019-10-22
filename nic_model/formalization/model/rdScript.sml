open HolKernel Parse boolLib bossLib;
open stateTheory;
open CPPI_RAMTheory;
open wordsTheory;

val _ = new_theory "rd";

val rd_6write_cp_def = Define `
  rd_6write_cp (env : environment) (nic : nic_state) =
  nic with <|
    regs := nic.regs with RX0_CP := 0xFFFFFFFCw;
    rd := nic.rd with state := rd_idle;
    rx := nic.rx with interrupt := if env.rd.assert_interrupt then T else nic.rx.interrupt;
    interrupt := if env.rd.assert_interrupt then T else nic.interrupt
  |>`;

val RD_WRITE_CURRENT_BD_PA_def = Define `
  RD_WRITE_CURRENT_BD_PA (nic : nic_state) = nic.rx.current_bd_pa <> 0w`;

val rd_5clear_owner_and_hdp_def = Define `
  rd_5clear_owner_and_hdp (nic : nic_state) =
  nic with <|
    rd := nic.rd with state := rd_write_cp;
    regs := nic.regs with <|
      RX0_CP := 0w;
      CPPI_RAM :=
        if RD_WRITE_CURRENT_BD_PA nic then
          clear_own nic.regs.CPPI_RAM nic.rx.current_bd_pa
        else
          nic.regs.CPPI_RAM|>;
    rx := nic.rx with <|
      current_bd_pa := 0w;
      sop_bd_pa := 0w
    |>
  |>`;

val rd_4set_td_def = Define `
  rd_4set_td (nic : nic_state) =
  if RD_WRITE_CURRENT_BD_PA nic then
    nic with <|
      rd := nic.rd with state := rd_clear_owner_and_hdp;
      regs := nic.regs with CPPI_RAM := set_td nic.regs.CPPI_RAM nic.rx.current_bd_pa
    |>
  else
    rd_5clear_owner_and_hdp nic`;

val rd_3set_eoq_def = Define `
  rd_3set_eoq (env : environment) (nic : nic_state) =
  if env.rd.set_eoq /\ RD_WRITE_CURRENT_BD_PA nic then
    nic with <|
      rd := nic.rd with state := rd_set_td;
      regs := nic.regs with CPPI_RAM := set_eoq nic.regs.CPPI_RAM nic.rx.current_bd_pa
    |>
  else
    rd_4set_td nic`;

val rd_2set_eop_def = Define `
  rd_2set_eop (env : environment) (nic : nic_state) =
  if env.rd.set_eop /\ RD_WRITE_CURRENT_BD_PA nic then
    nic with <|
      rd := nic.rd with state := rd_set_eoq;
      regs := nic.regs with CPPI_RAM := set_eop nic.regs.CPPI_RAM nic.rx.current_bd_pa
    |>
  else
    rd_3set_eoq env nic`;

val rd_1set_sop_def = Define `
  rd_1set_sop (env : environment) (nic : nic_state) =
  if env.rd.set_sop /\ RD_WRITE_CURRENT_BD_PA nic then
    nic with <|
      rd := nic.rd with state := rd_set_eop;
      regs := nic.regs with CPPI_RAM := set_sop nic.regs.CPPI_RAM nic.rx.current_bd_pa
    |>
  else
   rd_2set_eop env nic`;

val rd_0idle_def = Define `
  rd_0idle nic = nic with dead := T`;

val rd_transition_case_def = Define `
  (rd_transition_case rd_idle                env nic = rd_0idle                    nic) /\
  (rd_transition_case rd_set_sop             env nic = rd_1set_sop             env nic) /\
  (rd_transition_case rd_set_eop             env nic = rd_2set_eop             env nic) /\
  (rd_transition_case rd_set_eoq             env nic = rd_3set_eoq             env nic) /\
  (rd_transition_case rd_set_td              env nic = rd_4set_td                  nic) /\
  (rd_transition_case rd_clear_owner_and_hdp env nic = rd_5clear_owner_and_hdp     nic) /\
  (rd_transition_case rd_write_cp            env nic = rd_6write_cp            env nic)`;

val rd_transition_def = Define `
  rd_transition (env : environment) (nic : nic_state) =
  rd_transition_case nic.rd.state env nic`;

val _ = export_theory();

