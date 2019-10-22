open HolKernel Parse boolLib bossLib;
open wordsTheory; (* Contains the definition of the word datatype. *)
open wordsLib; (* Enables EVAL ``(7w :word4) + (2w :word4)`` *)
open stateTheory; (* Contains the definition of the state. *)
open CPPI_RAMTheory;

val _ = new_theory "tx";

(*
 * True if and only if the transmission automation expects a SOP when the
 * current buffer descriptor bd is a SOP, and when the current buffer
 * descriptor is a SOP then the transmission automation expects a SOP.
 *)
val TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP_def = Define `
  TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP (bd : bd_data) (tx : tx_state) =
  (tx.expects_sop = bd.sop)`;

(*
 * True if and only if the current sum of the buffer length fields of the
 * current frame under transmission results in an overflow with respect to the
 * size of the packet length field.
 *)
val TX_BUFFER_LENGTH_OVERFLOW_def = Define `
  TX_BUFFER_LENGTH_OVERFLOW (bd : bd_data) (tx : tx_state) =
  (bd.sop ==> bd.bl >=+ 2048w) /\
  (~bd.sop ==> tx.sum_buffer_length + bd.bl >=+ 2048w)`;

(*
 * True if and only if the buffer descriptor bd is not an EOP or, if it is an
 * EOP, then the sum of the buffer length fields of the current frame is equal
 * to the packet length field of the corresponding SOP buffer descriptor, where
 * the buffer offset field of the SOP is considered.
 *)
val TX_CONSISTENT_SUM_BUFFER_LENGTH_def = Define `
  TX_CONSISTENT_SUM_BUFFER_LENGTH (bd : bd_data) (tx : tx_state) =
  (bd.eop /\ bd.sop ==> (bd.bl = bd.pl)) /\
  (bd.eop /\ ~bd.sop ==> (tx.sum_buffer_length + bd.bl = tx.sop_packet_length))`;

(*
 * True if and only if the configuration of the current transmission buffer
 * descriptor is well-defined with respect to the previous buffer descriptors
 * of the current frame under transmission.
 *)
val TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs_def = Define `
  TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs (bd : bd_data) (tx : tx_state) =
  TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP bd tx /\
  ~TX_BUFFER_LENGTH_OVERFLOW bd tx /\
  TX_CONSISTENT_SUM_BUFFER_LENGTH bd tx`;

(*
 * True if and only if bd is a SOP buffer descriptor with its ownership bit
 * cleared.
 *)
val TX_SOP_WITH_NOT_OWNER_SET_def = Define `
  TX_SOP_WITH_NOT_OWNER_SET (bd : bd_data) = bd.sop /\ ~bd.own`;

(*
 * True if and only if bd is a SOP with its buffer offset field being greater
 * than or equal to the buffer length field.
 *)
val TX_SOP_BO_GEQ_BL_def = Define `TX_SOP_BO_GEQ_BL (bd : bd_data) =
  bd.sop /\ bd.bo >=+ bd.bl`;

(*
 * True if and only if the buffer length if of the buffer descriptor is
 * strictly greater than zero.
 *)
val TX_BL_GT_ZERO_def = Define `TX_BL_GT_ZERO (bd : bd_data) = bd.bl >+ 0w`;

(*
 * True if and only if bd is an EOP buffer descriptor with its EOQ bit set.
 *)
val TX_EOP_WITH_EOQ_SET_def = Define `
  TX_EOP_WITH_EOQ_SET (bd : bd_data) = bd.eop /\ bd.eoq`;

(*
 * True if and only if the end addresses of the buffer addressed by the buffer
 * descriptor are within the physical address space allocated to RAM.
 *)
val TX_BUFFER_START_END_IN_RAM_def = Define `TX_BUFFER_START_END_IN_RAM (bd : bd_data) =
  let bo = if bd.sop then bd.bo else 0w
  in
  BBB_RAM_START <=+ bd.bp + bo /\ bd.bp + bo + bd.bl - 1w <+ BBB_RAM_END`;

(*
 * True if and only if the buffer addresses identified by the buffer descriptor
 * overflows with respect to 2^32 modulo calculation. This occurs if at least
 * one of the following two cases is true:
 * -bp + bo <+ bp: The start address overflows.
 * -bp + bo + bl - 1 <+ bp + bo: The end address overflows.
 *)
val TX_BUFFER_WRAP_OVERFLOW_def = Define `TX_BUFFER_WRAP_OVERFLOW (bd : bd_data) =
  let bo = if bd.sop then bd.bo else 0w
  in
  bd.bp + bo <+ bd.bp \/
  bd.bp + bo + (bd.bl - 1w) <+ bd.bp + bo`;

(*
 * True if and only if the buffer descriptor is last but not an EOP.
 *)
val TX_BD_LAST_NOT_EOP_def = Define `TX_BD_LAST_NOT_EOP (bd : bd_data) =
  LAST_BD bd /\ ~bd.eop`;

(*
 * True if and only if the configuration of the current transmission buffer
 * descriptor is well-defined. That is, does not cause by itself the
 * transmission automaton to enter an undefined state.
 *)
val TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_def = Define `
  TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (bd : bd_data) =
  ~TX_SOP_WITH_NOT_OWNER_SET bd /\
  ~TX_SOP_BO_GEQ_BL bd /\
  TX_BL_GT_ZERO bd /\
  ~TX_EOP_WITH_EOQ_SET bd /\
  TX_BUFFER_START_END_IN_RAM bd /\
  ~TX_BUFFER_WRAP_OVERFLOW bd /\
  ~TX_BD_LAST_NOT_EOP bd`;

(*
 * Fetches the next buffer descriptors, checks that it cannot cause undefined
 * behavior, and initializes some state components used later.
 *)
val tx_1fetch_next_bd_def = Define `
  tx_1fetch_next_bd (nic : nic_state) =
    if ~BD_LOCATION_DEFINED nic.tx.current_bd_pa then
      nic with dead := T
    else
      let current_bd = tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM
      in
      if ~TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED_WITH_PREVIOUS_FRAME_BDs current_bd nic.tx then
        nic with dead := T
      else if ~TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED current_bd then
        nic with dead := T
      else
        let bp = current_bd.bp
        and bo = current_bd.bo
        and bl = current_bd.bl
        and pl = current_bd.pl
        and sop = current_bd.sop
        in
        nic with tx := nic.tx with <|
          current_bd := current_bd;
          sop_packet_length := if sop then pl else nic.tx.sop_packet_length;
          sum_buffer_length := if sop then bl else nic.tx.sum_buffer_length + bl;
          pa_of_next_memory_buffer_byte := if sop then bp + bo else bp;
          number_of_buffer_bytes_left_to_request := bl;
          state := tx_issue_next_memory_read_request
        |>`;

(*
 * Issues the next memory read reply.
 *)
val tx_2issue_next_memory_read_request_def = Define `
  tx_2issue_next_memory_read_request (nic : nic_state) =
  let mr' = <|
    pa := nic.tx.pa_of_next_memory_buffer_byte;
    v := NONE|>
  and nic = nic with tx := nic.tx with <|
    pa_of_next_memory_buffer_byte := nic.tx.pa_of_next_memory_buffer_byte + 1w;
    number_of_buffer_bytes_left_to_request := nic.tx.number_of_buffer_bytes_left_to_request - 1w;
    state := tx_process_memory_read_reply|>
  in
  (nic, SOME mr')`;

(*
 * True if and only if there are no bytes left to request.
 *)
val TX_ALL_BYTES_REQUESTED_def = Define `TX_ALL_BYTES_REQUESTED (tx : tx_state) =
  (tx.number_of_buffer_bytes_left_to_request = 0w)`;

(*
 * Processes the memory read request reply. Assumes that the device model
 * framework connecting all computer system models (CPU, memory and
 * I/O-devices) delivers memory read request replies correctly (that is, the
 * value of the memory location requested to read.
 *)
val tx_3process_memory_read_reply_def = Define `
  tx_3process_memory_read_reply (mem_req : memory_request) (nic : nic_state) =
  if TX_ALL_BYTES_REQUESTED nic.tx then
    if ~nic.tx.current_bd.eop then
      nic with tx := nic.tx with <|
        current_bd_pa := nic.tx.current_bd.ndp;
        expects_sop := F;
        state := tx_fetch_next_bd
      |>
    else
      nic with tx := nic.tx with <|
        eop_bd_pa := nic.tx.current_bd_pa;
        state := tx_post_process
      |>
  else
    nic with tx := nic.tx with state := tx_issue_next_memory_read_request`;

(*
 * Starts post-processing of a transmitted frame:
 * -If the current buffer descriptor is last in the queue, then the EOQ bit is
 *  set.
 * -If the current buffer descriptor is not last in the queue, then the
 *  ownership bit is cleared of the SOP buffer descriptor of the transmitted
 *  frame.
 *)
val tx_4post_process_def = Define `
  tx_4post_process (nic : nic_state) =
    if LAST_BD nic.tx.current_bd then
      nic with <|
        regs := nic.regs with CPPI_RAM := set_eoq nic.regs.CPPI_RAM nic.tx.current_bd_pa;
        tx := nic.tx with state := tx_clear_owner_and_hdp
      |>
    else
      nic with <|
        regs := nic.regs with CPPI_RAM := clear_own nic.regs.CPPI_RAM nic.tx.sop_bd_pa;
        tx := nic.tx with <|
          current_bd_pa := nic.tx.current_bd.ndp;
          sop_bd_pa := nic.tx.current_bd.ndp;
          expects_sop := T;
          state := tx_write_cp
        |>
      |>`;

(*
 * Clears the ownership bit of the SOP buffer descriptor of the transmitted
 * frame, and clears the TX0_HDP register.
 *)
val tx_5clear_owner_and_hdp_def = Define `
  tx_5clear_owner_and_hdp (nic : nic_state) =
    nic with <|
      regs := nic.regs with <|
        CPPI_RAM := clear_own nic.regs.CPPI_RAM nic.tx.sop_bd_pa;
        TX0_HDP := 0w
      |>;
      tx := nic.tx with <|
        current_bd_pa := 0w;
        sop_bd_pa := 0w;
        expects_sop := F;
        state := tx_write_cp
      |>
    |>`;

(*
 * Writes the physical address of the current buffer descriptor to the TX0_CP
 * register.
 *)
val tx_6write_cp_def = Define `
  tx_6write_cp (env : environment) (nic : nic_state) =
  nic with <|
    regs := nic.regs with TX0_CP := nic.tx.eop_bd_pa;
    interrupt := if env.tx.assert_interrupt then T else nic.interrupt;
    tx := nic.tx with <|
      interrupt := if env.tx.assert_interrupt then T else nic.tx.interrupt;
      state :=
        (* Must be nic.tx.current_bd_pa to check end of queue in this state, since
           software might write it when the transmission automaton is in this
           state. *)
        if (nic.tx.current_bd_pa = 0w) \/ (nic.it.state = it_reset) \/ (nic.td.state <> td_set_eoq) then
         tx_idle
        else
         tx_fetch_next_bd
    |>
  |>`;

(*
 * The "autonomous" transition function of the transmission automaton.
 *)
val tx_transition_def = Define `
  tx_transition (env : environment) (nic : nic_state) =
  case nic.tx.state of
    | tx_idle => (nic with dead := T, NONE)
    | tx_fetch_next_bd => (tx_1fetch_next_bd nic, NONE)
    | tx_issue_next_memory_read_request => tx_2issue_next_memory_read_request nic
    | tx_process_memory_read_reply => (nic with dead := T, NONE)
    | tx_post_process => (tx_4post_process nic, NONE)
    | tx_clear_owner_and_hdp => (tx_5clear_owner_and_hdp nic, NONE)
    | tx_write_cp => (tx_6write_cp env nic, NONE)`;

val _ = export_theory();
