open HolKernel Parse boolLib bossLib;
open wordsTheory;
open wordsLib; (* Enables pretty printing of words in hexadecimal notation. *)
open address_spaceTheory;

val _ = new_theory "CPPI_RAM";

type_abbrev ("cppi_ram_type", ``: 13 word -> 8 word``);

type_abbrev ("bd_pa_type", ``: 32 word``);

(*
 * Datatype for buffer descriptors. Only relevant fields are included and the
 * teardown bit.
 *)
val _ = Datatype `bd_data = <|
  ndp : 32 word;   (* Next descriptor pointer *)
  bp : 32 word;    (* Buffer pointer *)
  bl : 32 word;    (* Buffer length in lower 16(TX)/11(RX) bits *)
  bo : 32 word;    (* Buffer offset in lower 16(TX)/11(RX) bits *)
  pl : 32 word;    (* Packet length in lower 11 bits *)
  pass_crc : bool; (* RX *)
  td : bool;       (* Teardown *)
  eoq : bool;      (* End of queue *)
  own : bool;      (* Ownership *)
  eop : bool;      (* End of packet *)
  sop : bool       (* Start of packet *)
  |>`;

(*
 * True if and only if bd is the last buffer descriptor in a queue it resides
 * in. That is, its next descriptor pointer is equal to zero.
 *)
val LAST_BD_def = Define `LAST_BD (bd : bd_data) = (bd.ndp = 0w)`;

(*
 * True if and only if all bytes of a buffer descriptor starting at physical
 * address bd_pa are located inside CPPI_RAM. CPPI_RAM_END is subtracted by
 * 15, instead of bd_pa added with 15, to avoid overflow.
 *)
val BD_IN_CPPI_RAM_def = Define `
  BD_IN_CPPI_RAM (bd_pa : 32 word) =
    CPPI_RAM_START <=+ bd_pa /\ bd_pa <+ CPPI_RAM_END - 0xFw`;

(*
 * True if and only if bd_pa is a well-defined physical buffer descriptor
 * address.
 *)
val BD_LOCATION_DEFINED_def = Define `
  BD_LOCATION_DEFINED (bd_pa : 32 word) = WORD32_ALIGNED bd_pa /\ BD_IN_CPPI_RAM bd_pa`;

(*
 * Given a 32-bit physical address, the corresponding 13-bit CPPI_RAM offset is
 * returned.
 *)
val pa_to_cppi_ram_offset = Define `
  pa_to_cppi_ram_offset bd_pa = (word_extract 12 0) (bd_pa - CPPI_RAM_START) : 13 word`;

(*
 * Reads a 32-bit word in CPPI_RAM with word offset word_index with respect to
 * the physical address bd_pa. NOTE THAT THE ORDER OF CONCATENATION IS CORRECT!
 *)
val read_bd_word_def = Define `
  read_bd_word (bd_pa : 32 word) (word_index : 32 word) (CPPI_RAM : 13 word -> 8 word) =
    let word_byte_offset = (word_index << 2)
    in
    let b0 = CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + word_byte_offset + 0w))
    and b1 = CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + word_byte_offset + 1w))
    and b2 = CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + word_byte_offset + 2w))
    and b3 = CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + word_byte_offset + 3w))
    in
    concat_word_list [b0; b1; b2; b3] : 32 word`;

(*
 * Writes the 32-bit word value to CPPI_RAM at physical address pa.
 *)
val write_32bit_word_def = Define `
  write_32bit_word (value : 32 word) (pa : 32 word) (CPPI_RAM : cppi_ram_type) =
  let byte0 = ((7 >< 0) value) : 8 word
  and byte1 = ((15 >< 8) value) : 8 word
  and byte2 = ((23 >< 16) value) : 8 word
  and byte3 = ((31 >< 24) value) : 8 word
  and cppi_ram_offset_byte0 = pa_to_cppi_ram_offset (pa + 0w)
  and cppi_ram_offset_byte1 = pa_to_cppi_ram_offset (pa + 1w)
  and cppi_ram_offset_byte2 = pa_to_cppi_ram_offset (pa + 2w)
  and cppi_ram_offset_byte3 = pa_to_cppi_ram_offset (pa + 3w)
  in
  let CPPI_RAM0 = (cppi_ram_offset_byte0 =+ byte0) CPPI_RAM in
  let CPPI_RAM1 = (cppi_ram_offset_byte1 =+ byte1) CPPI_RAM0 in
  let CPPI_RAM2 = (cppi_ram_offset_byte2 =+ byte2) CPPI_RAM1 in
  let CPPI_RAM3 = (cppi_ram_offset_byte3 =+ byte3) CPPI_RAM2 in
    CPPI_RAM3`;

(* 
 * Reads a transmission buffer descriptor and returns a bd data structure
 * populated with the corresponding field values.
 *)
val tx_read_bd_def = Define `tx_read_bd (bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) =
  let tx_buffer_length (bd_word2 : 32 word) = (15 -- 0) bd_word2
  and tx_buffer_offset (bd_word2 : 32 word) = (31 -- 16) bd_word2
  and packet_length (bd_word3 : 32 word) = (10 -- 0) bd_word3
  and TD (bd_word3 : 32 word) = (((27 -- 27) bd_word3) = 0x1w)
  and EOQ (bd_word3 : 32 word) = (((28 -- 28) bd_word3) = 0x1w)
  and OWN (bd_word3 : 32 word) = (((29 -- 29) bd_word3) = 0x1w)
  and EOP (bd_word3 : 32 word) = (((30 -- 30) bd_word3) = 0x1w)
  and SOP (bd_word3 : 32 word) = (((31 -- 31) bd_word3) = 0x1w)
  and bd_word0 = read_bd_word bd_pa 0w CPPI_RAM
  and bd_word1 = read_bd_word bd_pa 1w CPPI_RAM
  and bd_word2 = read_bd_word bd_pa 2w CPPI_RAM
  and bd_word3 = read_bd_word bd_pa 3w CPPI_RAM
  in
  <|ndp := bd_word0;
    bp := bd_word1;
    bl := tx_buffer_length bd_word2;
    bo := tx_buffer_offset bd_word2;
    pl := packet_length bd_word3;
    pass_crc := F; (* Unused field for transmission buffer descriptors. *)
    td := TD bd_word3;
    eoq := EOQ bd_word3;
    own := OWN bd_word3;
    eop := EOP bd_word3;
    sop := SOP bd_word3
  |>`;

(* 
 * Reads a reception buffer descriptor and returns a bd data structure
 * populated with the corresponding field values.
 *)
val rx_read_bd_def = Define `rx_read_bd (bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) =
  let rx_buffer_length (bd_word2 : 32 word) = (10 -- 0) bd_word2
  and rx_buffer_offset (bd_word2 : 32 word) = (26 -- 16) bd_word2
  and packet_length (bd_word3 : 32 word) = (10 -- 0) bd_word3
  and TD (bd_word3 : 32 word) = (((27 -- 27) bd_word3) = 0x1w)
  and pass_crc (bd_word3 : 32 word) = (((26 -- 26) bd_word3) = 0x1w)
  and EOQ (bd_word3 : 32 word) = (((28 -- 28) bd_word3) = 0x1w)
  and OWN (bd_word3 : 32 word) = (((29 -- 29) bd_word3) = 0x1w)
  and EOP (bd_word3 : 32 word) = (((30 -- 30) bd_word3) = 0x1w)
  and SOP (bd_word3 : 32 word) = (((31 -- 31) bd_word3) = 0x1w)
  and bd_word0 = read_bd_word bd_pa 0w CPPI_RAM
  and bd_word1 = read_bd_word bd_pa 1w CPPI_RAM
  and bd_word2 = read_bd_word bd_pa 2w CPPI_RAM
  and bd_word3 = read_bd_word bd_pa 3w CPPI_RAM
  in
  <|ndp := bd_word0;
    bp := bd_word1;
    bl := rx_buffer_length bd_word2;
    bo := rx_buffer_offset bd_word2;
    pl := packet_length bd_word3;
    pass_crc := pass_crc bd_word3;
    td := TD bd_word3;
    eoq := EOQ bd_word3;
    own := OWN bd_word3;
    eop := EOP bd_word3;
    sop := SOP bd_word3
  |>`;

(*
 * Sets the EOQ bit in buffer descriptor at physical address bd_pa.
 *)
val set_eoq_def = Define `
  set_eoq (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  in
  let value = CPPI_RAM cppi_ram_offset || 0x10w
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Clears the ownership bit in the buffer descriptor at physical address bd_pa.
 *)
val clear_own_def = Define `
  clear_own (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  in
  let value = CPPI_RAM cppi_ram_offset && 0b11011111w
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the packet_error field of the buffer descriptor at physical address
 * bd_pa.
 *)
val write_packet_error_def = Define `
  write_packet_error (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (packet_error : 2 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 14w)
  and packet_error = w2w packet_error : 8 word << 4
  in
  let new_value = (CPPI_RAM cppi_ram_offset && 0b11001111w) || packet_error
  in
  (cppi_ram_offset =+ new_value) CPPI_RAM`;

(*
 * Writes the rx_vlan_encap field of the buffer descriptor at physical address
 * bd_pa.
 *)
val write_rx_vlan_encap_def = Define `
  write_rx_vlan_encap (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (rx_vlan_encap : 1 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 14w)
  and rx_vlan_encap = w2w rx_vlan_encap : 8 word << 3
  in
  let new_value = (CPPI_RAM cppi_ram_offset && 0b11110111w) || rx_vlan_encap
  in
  (cppi_ram_offset =+ new_value) CPPI_RAM`;

(*
 * Writes the from port field of the buffer descriptor at physical address
 * bd_pa.
 *)
val write_from_port_def = Define `
  write_from_port (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (from_port : 3 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 14w)
  and from_port = w2w from_port : 8 word
  in
  let new_value = (CPPI_RAM cppi_ram_offset && 0b11111000w) || from_port
  in
  (cppi_ram_offset =+ new_value) CPPI_RAM`;

(*
 * Writes the buffer length field according to the reception format of the
 * buffer descriptor at physical address bd_pa.
 *)
val write_rx_buffer_length_def = Define `
  write_rx_buffer_length (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (buffer_length : 32 word) =
  let cppi_ram_offset7_0 = pa_to_cppi_ram_offset (bd_pa + 8w)
  and value7_0 = (7 >< 0) buffer_length : 8 word
  and cppi_ram_offset10_8 = pa_to_cppi_ram_offset (bd_pa + 9w)
  in
  let value10_8 = (CPPI_RAM cppi_ram_offset10_8 && 0b11111000w) ||
                  (10 >< 8) buffer_length : 8 word
  in
  let CPPI_RAM7_0 = (cppi_ram_offset7_0 =+ value7_0) CPPI_RAM
  in
  (cppi_ram_offset10_8 =+ value10_8) CPPI_RAM7_0`;

(*
 * Sets the EOP field of the buffer descriptor at physical address bd_pa.
 *)
val set_eop_def = Define `
  set_eop (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  in
  let value = (CPPI_RAM cppi_ram_offset) || 0b01000000w
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the buffer offset field according to the reception format of the
 * buffer descriptor at physical address bd_pa.
 *)
val write_rx_buffer_offset_def = Define `
  write_rx_buffer_offset (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (buffer_offset : 32 word) =
  let cppi_ram_offset7_0 = pa_to_cppi_ram_offset (bd_pa + 10w)
  and value7_0 = (7 >< 0) buffer_offset : 8 word
  and cppi_ram_offset10_8 = pa_to_cppi_ram_offset (bd_pa + 11w)
  in
  let value10_8 = (CPPI_RAM cppi_ram_offset10_8 && 0b11111000w) ||
                  (10 >< 8) buffer_offset : 8 word
  in
  let CPPI_RAM7_0 = (cppi_ram_offset7_0 =+ value7_0) CPPI_RAM
  in
  (cppi_ram_offset10_8 =+ value10_8) CPPI_RAM7_0`;

(*
 * Sets the SOP field of the buffer descriptor at physical address bd_pa.
 *)
val set_sop_def = Define `
  set_sop (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  in
  let value = (CPPI_RAM cppi_ram_offset) || 0b10000000w
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the pass crc field of the buffer descriptor at physical address bd_pa.
 *)
val write_pass_crc_def = Define `
  write_pass_crc (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (pass_crc : 1 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  and pass_crc = w2w pass_crc << 2
  in
  let value = (CPPI_RAM cppi_ram_offset && 0b11111011w) || pass_crc
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the long field of the reception buffer descriptor at physical address
 * bd_pa.
 *)
val write_rx_long_def = Define `
  write_rx_long (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (long : 1 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  and long = w2w long << 1
  in
  let value = (CPPI_RAM cppi_ram_offset && 0b11111101w) || long
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the short field of the reception buffer descriptor at physical address
 * bd_pa.
 *)
val write_rx_short_def = Define `
  write_rx_short (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (short : 1 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  and short = w2w short
  in
  let value = (CPPI_RAM cppi_ram_offset && 0b11111110w) || short
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the short field of the reception buffer descriptor at physical address
 * bd_pa.
 *)
val write_rx_mac_ctl_def = Define `
  write_rx_mac_ctl (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (mac_ctl : 1 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 14w)
  and mac_ctl = w2w mac_ctl << 7
  in
  let value = (CPPI_RAM cppi_ram_offset && 0b01111111w) || mac_ctl
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Writes the packet length field of the buffer descriptor at physical address
 * bd_pa.
 *)
val write_packet_length_def = Define `
  write_packet_length (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) (packet_length : 32 word) =
  let cppi_ram_offset7_0 = pa_to_cppi_ram_offset (bd_pa + 12w)
  and value7_0 = (7 >< 0) packet_length : 8 word
  and cppi_ram_offset10_8 = pa_to_cppi_ram_offset (bd_pa + 13w)
  in
  let value10_8 = (CPPI_RAM cppi_ram_offset10_8 && 0b11111000w) ||
                  (10 >< 8) packet_length : 8 word
  in
  let CPPI_RAM7_0 = (cppi_ram_offset7_0 =+ value7_0) CPPI_RAM
  in
  (cppi_ram_offset10_8 =+ value10_8) CPPI_RAM7_0`;

(*
 * Sets the overrun flag of the reception buffer descriptor at physical address
 * bd_pa.
 *)
val set_rx_overrun_def = Define `
  set_rx_overrun (CPPI_RAM : 13 word -> 8 word) (bd_pa : 32 word) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 14w)
  in
  let value = (CPPI_RAM cppi_ram_offset) || 0b01000000w
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

(*
 * Sets the teardown bit of the buffer descriptor at physical address bd_pa.
 *)
val set_td_def = Define `
  set_td (CPPI_RAM : cppi_ram_type) (bd_pa : bd_pa_type) =
  let cppi_ram_offset = pa_to_cppi_ram_offset (bd_pa + 15w)
  in
  let value = (CPPI_RAM cppi_ram_offset) || 0b00001000w
  in
  (cppi_ram_offset =+ value) CPPI_RAM`;

val _ = export_theory();

