open HolKernel Parse boolLib bossLib;
open stateTheory;
open CPPI_RAMTheory;

val _ = new_theory "register_write";

val write_tx_teardown_def = Define `
  write_tx_teardown (value : 32 word) (nic : nic_state) =
  let value = (2 >< 0) value : 3 word
  in
  if nic.it.state <> it_initialized \/ nic.td.state <> td_idle \/ value <> 0w then
    nic with dead := T
  else
    nic with td := nic.td with state := td_set_eoq`;

val write_rx_teardown_def = Define `
  write_rx_teardown (value : 32 word) (nic : nic_state) =
  let value = (2 >< 0) value : 3 word
  in
  if nic.it.state <> it_initialized \/ nic.rd.state <> rd_idle \/ value <> 0w then
    nic with dead := T
  else
    nic with rd := nic.rd with state := rd_set_sop`;
    
val write_cpdma_soft_reset_def = Define `
  write_cpdma_soft_reset (value : 32 word) (nic : nic_state) =
  let value = (0 >< 0) value : 1 word
  in
  case nic.it.state of
    | it_power_on =>
        if value = 0w then
          nic with dead := T
        else
          nic with <|
            regs := nic.regs with CPDMA_SOFT_RESET := 1w;
            it := nic.it with <|
              state := it_reset;
              tx0_hdp_initialized := F;
              rx0_hdp_initialized := F;
              tx0_cp_initialized := F;
              rx0_cp_initialized := F
            |>
          |>
    | it_reset => nic with dead := T
    | it_initialize_hdp_cp => nic with dead := T
    | it_idle =>
        if (value = 1w) /\ (nic.td.state <> td_idle \/ nic.rd.state <> rd_idle) then
          nic with dead := T
        else if value = 1w then
          nic with <|
            regs := nic.regs with CPDMA_SOFT_RESET := 1w;
            it := nic.it with <|
              state := it_reset;
              tx0_hdp_initialized := F;
              rx0_hdp_initialized := F;
              tx0_cp_initialized := F;
              rx0_cp_initialized := F
            |>
          |>
        else
          nic`;

val write_dmacontrol_def = Define `
  write_dmacontrol (value : 32 word) (nic : nic_state) =
  let value = (15 >< 0) value : 16 word
  in
    if nic.it.state <> it_initialized \/ value <> 0w then
      nic with dead := T
    else
      nic`;

val write_rx_buffer_offset_def = Define `
  write_rx_buffer_offset (value : 32 word) (nic : nic_state) =
  let value = (15 >< 0) value : 16 word
  in
    if nic.it.state <> it_initialized then
      nic with dead := T
    else
      nic with regs := nic.regs with RX_BUFFER_OFFSET := value`;

val write_tx0_hdp_def = Define `
  write_tx0_hdp (env : environment) (bd_pa : 32 word) (nic : nic_state) =
  case nic.it.state of
    | it_power_on => nic with dead := T
    | it_reset => nic with dead := T
    | it_initialize_hdp_cp => 
        if bd_pa <> 0w then
          nic with dead := T
        else
          nic with <|
            regs := nic.regs with TX0_HDP := 0w;
            tx := nic.tx with <|
              current_bd_pa := 0w;
              sop_bd_pa := 0w
            |>;
            it := nic.it with <|
              tx0_hdp_initialized := T;
              state :=
                if nic.it.rx0_hdp_initialized /\ nic.it.tx0_cp_initialized /\ nic.it.rx0_cp_initialized then
                  it_initialized
                else
                  it_initialize_hdp_cp
            |>
          |>
    | it_initialized =>
        if nic.regs.TX0_HDP <> 0w \/ nic.td.state <> td_idle then
          nic with dead := T
        else if bd_pa <> 0w then
          nic with <|
            regs := nic.regs with TX0_HDP := if env.reg_write.tx0_hdp_value = 0w then 1w else env.reg_write.tx0_hdp_value;
            tx := nic.tx with <| 
              current_bd_pa := bd_pa;
              sop_bd_pa := bd_pa;
              expects_sop := T;
              state := if nic.tx.state = tx_idle then tx_fetch_next_bd else nic.tx.state
	        |>
          |>
        else
          nic`;

val write_rx0_hdp_def = Define `
  write_rx0_hdp (env : environment) (bd_pa : 32 word) (nic : nic_state) =
  case nic.it.state of
    | it_power_on => nic with dead := T
    | it_reset => nic with dead := T
    | it_initialize_hdp_cp => 
        if bd_pa <> 0w then
          nic with dead := T
        else
          nic with <|
            regs := nic.regs with RX0_HDP := 0w;
            rx := nic.rx with <|
              current_bd_pa := 0w;
              sop_bd_pa := 0w
            |>;
            it := nic.it with <|
              rx0_hdp_initialized := T;
              state :=
                if nic.it.tx0_hdp_initialized /\ nic.it.tx0_cp_initialized /\ nic.it.rx0_cp_initialized then
                  it_initialized
                else
                  it_initialize_hdp_cp
            |>
          |>
    | it_initialized =>
        if nic.regs.RX0_HDP <> 0w \/ nic.rd.state <> rd_idle then
          nic with dead := T
        else if bd_pa <> 0w then
          nic with <|
            regs := nic.regs with RX0_HDP := if env.reg_write.rx0_hdp_value = 0w then 1w else env.reg_write.rx0_hdp_value;
            rx := nic.rx with <| 
              current_bd_pa := bd_pa;
              sop_bd_pa := bd_pa
	        |>
          |>
        else
          nic`;

val write_tx0_cp_def = Define `
  write_tx0_cp (env : environment) (bd_pa : 32 word) (nic : nic_state) =
  if nic.it.state <> it_initialized then (
    if (bd_pa = 0w) /\ (nic.it.state = it_initialize_hdp_cp) then
      nic with <|
        regs := nic.regs with TX0_CP := 0w;
        it := nic.it with <|
          tx0_cp_initialized := T;
          state :=
            if nic.it.tx0_hdp_initialized /\ nic.it.rx0_hdp_initialized /\ nic.it.rx0_cp_initialized then
              it_initialized
            else
              it_initialize_hdp_cp
        |>;
        tx := nic.tx with interrupt := if env.reg_write.tx0_cp_deassert_interrupt then F else nic.tx.interrupt;
        interrupt := if env.reg_write.tx0_cp_deassert_interrupt /\ ~nic.rx.interrupt then F else nic.interrupt
      |>
    else
      nic with dead := T)
  else
    nic with <|
      tx := nic.tx with interrupt := if nic.regs.TX0_CP = bd_pa then F else nic.tx.interrupt;
      interrupt := if (nic.regs.TX0_CP = bd_pa) /\ ~nic.rx.interrupt then F else nic.interrupt
    |>`;

val write_rx0_cp_def = Define `
  write_rx0_cp (env : environment) (bd_pa : 32 word) (nic : nic_state) =
  if nic.it.state <> it_initialized then (
    if (bd_pa = 0w) /\ (nic.it.state = it_initialize_hdp_cp) then
      nic with <|
        regs := nic.regs with RX0_CP := 0w;
        it := nic.it with <|
          rx0_cp_initialized := T;
          state :=
            if nic.it.tx0_hdp_initialized /\ nic.it.rx0_hdp_initialized /\ nic.it.tx0_cp_initialized then
              it_initialized
            else
              it_initialize_hdp_cp
        |>;
        rx := nic.rx with interrupt := if env.reg_write.rx0_cp_deassert_interrupt then F else nic.rx.interrupt;
        interrupt := if env.reg_write.rx0_cp_deassert_interrupt /\ ~nic.tx.interrupt then F else nic.interrupt
      |>
    else
      nic with dead := T)
  else
    nic with <|
      rx := nic.rx with interrupt := if nic.regs.RX0_CP = bd_pa then F else nic.rx.interrupt;
      interrupt := if (nic.regs.RX0_CP = bd_pa) /\ ~nic.tx.interrupt then F else nic.interrupt
    |>`;

val write_cppi_ram_def = Define `
  write_cppi_ram (pa : 32 word) (value : 32 word) (nic : nic_state) =
  nic with regs := nic.regs with CPPI_RAM := write_32bit_word value pa nic.regs.CPPI_RAM`;

val write_register_def = Define `
  write_register (env : environment) (pa : 32 word) (value : 32 word) (nic : nic_state) =
  if nic.dead then
    nic
  else if ~WORD32_ALIGNED pa then
    nic with dead := T
  else if NOT_ZERO_CHANNEL_HDP_BYTE pa /\ value <> 0w then
    nic with dead := T
  else if pa = TX_TEARDOWN_PA then
    write_tx_teardown value nic
  else if pa = RX_TEARDOWN_PA then
    write_rx_teardown value nic
  else if pa = CPDMA_SOFT_RESET_PA then
    write_cpdma_soft_reset value nic
  else if pa = DMACONTROL_PA then
    write_dmacontrol value nic
  else if pa = RX_BUFFER_OFFSET_PA then
    write_rx_buffer_offset value nic
  else if pa = TX0_HDP_PA then
    write_tx0_hdp env value nic
  else if pa = RX0_HDP_PA then
    write_rx0_hdp env value nic
  else if pa = TX0_CP_PA then
    write_tx0_cp env value nic
  else if pa = RX0_CP_PA then
    write_rx0_cp env value nic
  else if CPPI_RAM_BYTE_PA pa then
    write_cppi_ram pa value nic
  else
    nic`;

val _ = export_theory();

