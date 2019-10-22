open HolKernel Parse boolLib bossLib;
open stateTheory;
open CPPI_RAMTheory;
open wordsTheory;
open wordsLib;

val _ = new_theory "rx";

val RX_BUFFER_IN_BBB_RAM_def = Define `
  RX_BUFFER_IN_BBB_RAM (bd : bd_data) (bo : 32 word) =
  let start_pa = bd.bp + bo
  and length = bd.bl - bo
  in
  !offset : 32 word.
  offset <+ length
  ==>
  BBB_RAM_START <=+ start_pa + offset /\
  start_pa + offset <+ BBB_RAM_END`;

val RX_BUFFER_OVERFLOW_def = Define `
  RX_BUFFER_OVERFLOW (bd : bd_data) (bo : 32 word) =
  let start_pa = bd.bp + bo
  and length = bd.bl - bo
  in
  length >+ 0w
  ==>
  ?offset : 32 word.
  offset <+ length /\
  start_pa + offset <+ start_pa`;

val RX_BD_WELL_DEFINED_def = Define `
  RX_BD_WELL_DEFINED (bd : bd_data) (sop : bool) (rx_buffer_offset_register : 16 word) =
  let bo = if sop then w2w rx_buffer_offset_register : 32 word else 0w
  in
  (bd.bo = 0w) /\ bd.bl >+ bo /\
  ~bd.sop /\ ~bd.eop /\ bd.own /\ ~bd.eoq /\
  RX_BUFFER_IN_BBB_RAM bd bo /\
  ~RX_BUFFER_OVERFLOW bd bo /\
  (sop ==> ~bd.pass_crc)`;

val RX_CURRENT_BD_SOP_def = Define `
  RX_CURRENT_BD_SOP (rx : rx_state) = (rx.current_bd_pa = rx.sop_bd_pa)`;

val rx_1fetch_next_bd_def = Define `
  rx_1fetch_next_bd (nic : nic_state) =
  if ~BD_LOCATION_DEFINED nic.rx.current_bd_pa then
    nic with dead := T
  else
    let current_bd = rx_read_bd nic.rx.current_bd_pa nic.regs.CPPI_RAM
    and sop = RX_CURRENT_BD_SOP nic.rx
    and bo = w2w nic.regs.RX_BUFFER_OFFSET : 32 word
    in
    if ~RX_BD_WELL_DEFINED current_bd sop nic.regs.RX_BUFFER_OFFSET then
      nic with dead := T
    else
      nic with rx := nic.rx with <|
        current_bd := current_bd;
        current_bd_number_of_stored_bytes := 0w;
        next_buffer_byte_address := current_bd.bp + if sop then bo else 0w;
        current_bd_size := current_bd.bl - if sop then bo else 0w;
        sop_buffer_offset := if sop then bo else nic.rx.sop_buffer_offset;
        sop_buffer_used_length := if sop then current_bd.bl - bo else nic.rx.sop_buffer_used_length;
        state := rx_issue_next_memory_write_request|>`;

val RX_STORE_MORE_BYTES_def = Define `
  RX_STORE_MORE_BYTES (rx : rx_state) =
  rx.frame_bytes_left >+ 1w /\
  rx.current_bd_number_of_stored_bytes <+ rx.current_bd_size - 1w`;

val rx_2issue_next_memory_write_request_def = Define `
  rx_2issue_next_memory_write_request (nic : nic_state) =
  let mr' = <|
    pa := nic.rx.next_buffer_byte_address;
    v := SOME (HD nic.rx.frame) |>
  and nic = nic with rx := nic.rx with <|
    frame := TL nic.rx.frame;
    frame_bytes_left := nic.rx.frame_bytes_left - 1w;
    current_bd_number_of_stored_bytes := nic.rx.current_bd_number_of_stored_bytes + 1w;
    next_buffer_byte_address := nic.rx.next_buffer_byte_address + 1w;
    state := if RX_STORE_MORE_BYTES nic.rx then rx_issue_next_memory_write_request else rx_write_packet_error|>
  in (nic, SOME mr')`;

val rx_3write_packet_error_def = Define `
  rx_3write_packet_error (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_rx_vlan_encap;
    regs := nic.regs with CPPI_RAM := write_packet_error nic.regs.CPPI_RAM nic.rx.current_bd_pa env.rx.packet_error|>`;

val rx_4write_rx_vlan_encap_def = Define `
  rx_4write_rx_vlan_encap (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_from_port;
    regs := nic.regs with CPPI_RAM := write_rx_vlan_encap nic.regs.CPPI_RAM nic.rx.current_bd_pa env.rx.rx_vlan_encap|>`;

val RX_FRAME_STORED_def = Define `
  RX_FRAME_STORED (rx : rx_state) = (rx.frame_bytes_left = 0w)`;

val rx_5write_from_port_def = Define `
  rx_5write_from_port (env : environment) (nic : nic_state) =
  let CPPI_RAM = write_from_port nic.regs.CPPI_RAM nic.rx.current_bd_pa env.rx.from_port
  in
  if RX_FRAME_STORED nic.rx then
    nic with <|
      rx := nic.rx with <|
        eop_bd_pa := nic.rx.current_bd_pa;
        overrun := F;
        state := rx_write_eop_buffer_length|>;
      regs := nic.regs with CPPI_RAM := CPPI_RAM|>
  else if LAST_BD nic.rx.current_bd then
    nic with <|
      rx := nic.rx with <|
        eop_bd_pa := nic.rx.current_bd_pa;
        overrun := T;
        state := rx_write_eop_buffer_length|>;
      regs := nic.regs with CPPI_RAM := CPPI_RAM|>
  else
    nic with <|
      rx := nic.rx with <|
        current_bd_pa := nic.rx.current_bd.ndp;
        state := rx_fetch_next_bd|>;
      regs := nic.regs with CPPI_RAM := CPPI_RAM|>`;

val rx_6write_eop_buffer_length_def = Define `
  rx_6write_eop_buffer_length (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_set_eop_eop;
    regs := nic.regs with CPPI_RAM := write_rx_buffer_length nic.regs.CPPI_RAM nic.rx.eop_bd_pa nic.rx.current_bd_number_of_stored_bytes|>`;

val rx_7set_eop_eop_def = Define `
  rx_7set_eop_eop (nic :nic_state) =
  nic with <|
    rx := nic.rx with state := rx_set_eop_eoq_or_write_sop_buffer_offset;
    regs := nic.regs with CPPI_RAM := set_eop nic.regs.CPPI_RAM nic.rx.eop_bd_pa|>`;

val rx_8set_eop_eoq_or_write_sop_buffer_offset_def = Define `
  rx_8set_eop_eoq_or_write_sop_buffer_offset (nic : nic_state) =
  if LAST_BD nic.rx.current_bd then
    nic with <|
      rx := nic.rx with state := rx_write_sop_buffer_offset;
      regs := nic.regs with CPPI_RAM := set_eoq nic.regs.CPPI_RAM nic.rx.eop_bd_pa|>
  else
    nic with <|
      rx := nic.rx with state := rx_write_sop_buffer_length;
      regs := nic.regs with CPPI_RAM := write_rx_buffer_offset nic.regs.CPPI_RAM nic.rx.sop_bd_pa nic.rx.sop_buffer_offset|>`;

val rx_9write_sop_buffer_offset_def = Define `
  rx_9write_sop_buffer_offset (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_sop_buffer_length;
    regs := nic.regs with CPPI_RAM := write_rx_buffer_offset nic.regs.CPPI_RAM nic.rx.sop_bd_pa nic.rx.sop_buffer_offset|>`;

val rx_10write_sop_buffer_length_def = Define `
  rx_10write_sop_buffer_length (nic : nic_state) =
  if nic.rx.sop_bd_pa = nic.rx.eop_bd_pa then
    nic with <|
      rx := nic.rx with state := rx_set_sop_sop;
      regs := nic.regs with CPPI_RAM := write_rx_buffer_length nic.regs.CPPI_RAM nic.rx.sop_bd_pa nic.rx.current_bd_number_of_stored_bytes|>
  else
    nic with <|
      rx := nic.rx with state := rx_set_sop_sop;
      regs := nic.regs with CPPI_RAM := write_rx_buffer_length nic.regs.CPPI_RAM nic.rx.sop_bd_pa nic.rx.sop_buffer_used_length|>`;

val rx_11set_sop_sop_def = Define `
  rx_11set_sop_sop (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_sop_pass_crc;
    regs := nic.regs with CPPI_RAM := set_sop nic.regs.CPPI_RAM nic.rx.sop_bd_pa|>`;

val rx_12write_sop_pass_crc_def = Define `
  rx_12write_sop_pass_crc (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_sop_long;
    regs := nic.regs with CPPI_RAM := write_pass_crc nic.regs.CPPI_RAM nic.rx.sop_bd_pa env.rx.pass_crc|>`;

val rx_13write_sop_long_def = Define `
  rx_13write_sop_long (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_sop_short;
    regs := nic.regs with CPPI_RAM := write_rx_long nic.regs.CPPI_RAM nic.rx.sop_bd_pa env.rx.long|>`;

val rx_14write_sop_short_def = Define `
  rx_14write_sop_short (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_sop_mac_ctl;
    regs := nic.regs with CPPI_RAM := write_rx_short nic.regs.CPPI_RAM nic.rx.sop_bd_pa env.rx.short|>`;

val rx_15write_sop_mac_ctl_def = Define `
  rx_15write_sop_mac_ctl (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_write_sop_packet_length;
    regs := nic.regs with CPPI_RAM := write_rx_mac_ctl nic.regs.CPPI_RAM nic.rx.sop_bd_pa env.rx.mac_ctl|>`;

val rx_16write_sop_packet_length = Define `
  rx_16write_sop_packet_length (nic : nic_state) =
  nic with <|
    rx := nic.rx with state := rx_set_sop_eop_overrun_or_clear_sop_owner_and_hdp;
    regs := nic.regs with CPPI_RAM := write_packet_length nic.regs.CPPI_RAM nic.rx.sop_bd_pa (nic.rx.frame_length - nic.rx.frame_bytes_left)|>`;

val rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp_def = Define `
  rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp (env : environment) (nic : nic_state) =
  if nic.rx.overrun then
    nic with <|
      rx := nic.rx with state := rx_clear_sop_owner_and_hdp;
      regs := nic.regs with CPPI_RAM :=
        let CPPI_RAM_sop = set_rx_overrun nic.regs.CPPI_RAM nic.rx.sop_bd_pa in
        let CPPI_RAM_eop = set_rx_overrun nic.regs.CPPI_RAM nic.rx.eop_bd_pa in
        let CPPI_RAM_sop_eop = set_rx_overrun CPPI_RAM_sop nic.rx.eop_bd_pa in
        case env.rx.sop_eop_both_overrun of
          | sop_overrun => CPPI_RAM_sop
          | eop_overrun => CPPI_RAM_eop
          | both_overrun => CPPI_RAM_sop_eop
    |>
  else
    nic with <|
      rx := nic.rx with <|
        state := rx_write_cp;
        current_bd_pa := nic.rx.current_bd.ndp;
        sop_bd_pa := nic.rx.current_bd.ndp|>;
      regs := nic.regs with <|
        CPPI_RAM := clear_own nic.regs.CPPI_RAM nic.rx.sop_bd_pa;
        RX0_HDP := if LAST_BD nic.rx.current_bd then 0w else nic.regs.RX0_HDP|>
    |>`;

val rx_18clear_sop_owner_and_hdp_def = Define `
  rx_18clear_sop_owner_and_hdp (nic : nic_state) =
  nic with <|
    rx := nic.rx with <|
      state := rx_write_cp;
      current_bd_pa := nic.rx.current_bd.ndp;
      sop_bd_pa := nic.rx.current_bd.ndp|>;
    regs := nic.regs with <|
      CPPI_RAM := clear_own nic.regs.CPPI_RAM nic.rx.sop_bd_pa;
      RX0_HDP := if LAST_BD nic.rx.current_bd then 0w else nic.regs.RX0_HDP|>
  |>`;

val rx_19write_cp_def = Define `
  rx_19write_cp (env : environment) (nic : nic_state) =
  nic with <|
    rx := nic.rx with <|
      state := rx_idle;
      interrupt := if env.rx.assert_interrupt then T else nic.rx.interrupt|>;
    regs := nic.regs with RX0_CP := nic.rx.eop_bd_pa;
    interrupt :=  if env.rx.assert_interrupt then T else nic.interrupt|>`;

val rx_0receive_new_frame_def = Define `
  rx_0receive_new_frame (env : environment) (nic : nic_state) =
  let nic = nic with rx := nic.rx with <|
    frame := env.rx.received_frame;
    frame_length := n2w (LENGTH env.rx.received_frame);
    frame_bytes_left := n2w (LENGTH env.rx.received_frame)|>
  in
  rx_1fetch_next_bd nic`;

val rx_transition_def = Define `
  rx_transition (env : environment) (nic : nic_state) =
  case nic.rx.state of
    | rx_idle => (rx_0receive_new_frame env nic, NONE)
    | rx_fetch_next_bd => (rx_1fetch_next_bd nic, NONE)
    | rx_issue_next_memory_write_request => rx_2issue_next_memory_write_request nic
    | rx_write_packet_error => (rx_3write_packet_error env nic, NONE)
    | rx_write_rx_vlan_encap => (rx_4write_rx_vlan_encap env nic, NONE)
    | rx_write_from_port => (rx_5write_from_port env nic, NONE)
    | rx_write_eop_buffer_length => (rx_6write_eop_buffer_length nic, NONE)
    | rx_set_eop_eop => (rx_7set_eop_eop nic, NONE)
    | rx_set_eop_eoq_or_write_sop_buffer_offset =>
        (rx_8set_eop_eoq_or_write_sop_buffer_offset nic, NONE)
    | rx_write_sop_buffer_offset => (rx_9write_sop_buffer_offset nic, NONE)
    | rx_write_sop_buffer_length => (rx_10write_sop_buffer_length nic, NONE)
    | rx_set_sop_sop => (rx_11set_sop_sop nic, NONE)
    | rx_write_sop_pass_crc => (rx_12write_sop_pass_crc env nic, NONE)
    | rx_write_sop_long => (rx_13write_sop_long env nic, NONE)
    | rx_write_sop_short => (rx_14write_sop_short env nic, NONE)
    | rx_write_sop_mac_ctl => (rx_15write_sop_mac_ctl env nic, NONE)
    | rx_write_sop_packet_length => (rx_16write_sop_packet_length nic, NONE)
    | rx_set_sop_eop_overrun_or_clear_sop_owner_and_hdp =>
        (rx_17set_sop_eop_overrun_or_clear_sop_owner_and_hdp env nic, NONE)
    | rx_clear_sop_owner_and_hdp => (rx_18clear_sop_owner_and_hdp nic, NONE)
    | rx_write_cp => (rx_19write_cp env nic, NONE)`;

val _ = export_theory();

