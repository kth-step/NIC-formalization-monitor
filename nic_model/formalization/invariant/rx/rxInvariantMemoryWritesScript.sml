open HolKernel Parse boolLib bossLib;
open CPPI_RAMTheory;
open stateTheory;
open rx_state_definitionsTheory;
open rx_bd_queueTheory;

val _ = new_theory "rxInvariantMemoryWrites";

(*
 * This file defines the parts of the reception invariant the ensures that
 * the NIC can only write writable memory.
 *
 * Writable memory is specified by the undefined predicate WRITABLE.
 *)

(*
 * The NIC may only write writable memory:
 * -Start address: current_bd.bp
 * -End address: current_bd.bp + current_bd.size - 1
 *
 * !pa. MEM pa [nic.rx.current_bd.ndp, nic.rx.current_bd.ndp + nic.rx.current_bd.size - 1) ==> WRITABLE pa
 *
 * Invariant implying that the buffer descriptor at bd_pa addresses writable memory.
 *)
val BD_ADDRESSES_WRITABLE_MEMORY_def = Define `
  BD_ADDRESSES_WRITABLE_MEMORY (bd_pa : 32 word)
                               (CPPI_RAM : 13 word -> 8 word)
                               (WRITABLE : 32 word -> bool) =
  let bd = rx_read_bd bd_pa CPPI_RAM
  in
  (!pa. bd.bp <=+ pa /\ pa <=+ bd.bp + (bd.bl - 1w) ==> WRITABLE pa)`;

val RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_def = Define `
  RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (q : 32 word list)
                                        (CPPI_RAM : 13 word -> 8 word)
                                        (WRITABLE : 32 word -> bool) =
  EVERY (\bd_pa. BD_ADDRESSES_WRITABLE_MEMORY bd_pa CPPI_RAM WRITABLE) q`;

val RX_INVARIANT_CURRENT_BUFFER_WRITABLE_def = Define `
  RX_INVARIANT_CURRENT_BUFFER_WRITABLE (nic : nic_state) (WRITABLE : 32 word -> bool) =
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic
  ==>
  !pa.
  nic.rx.current_bd.bp <=+ pa /\ pa <=+ nic.rx.current_bd.bp + (nic.rx.current_bd_size - 1w)
  ==>
  WRITABLE pa`;

val RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES_def = Define `
  RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic =
  (nic.rx.next_buffer_byte_address = nic.rx.current_bd.bp + nic.rx.current_bd_number_of_stored_bytes)`;

val RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_def = Define `
  RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES (nic : nic_state) =
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic
  ==>
  RX_NEXT_BUFFER_BYTE_ADDRESS_EQ_CURRENT_BD_BP_PLUS_CURRENT_BD_NUMBER_OF_STORED_BYTES nic`;

val RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD_def = Define `
  RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic =
  nic.rx.current_bd.bp <=+ nic.rx.next_buffer_byte_address /\
  nic.rx.next_buffer_byte_address <=+ nic.rx.current_bd.bp + (nic.rx.current_bd_size - 1w)`;

val RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER_def = Define `
  RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic =
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic
  ==>
  RX_NEXT_BUFFER_BYTE_ADDRESS_IN_CURRENT_BD nic`;

(*
 * Invariant of the reception automaton implying the NIC can only write to
 * writable memory, excluding undefined aspects.
 *)
val RX_INVARIANT_MEMORY_WRITABLE_def = Define `
  RX_INVARIANT_MEMORY_WRITABLE (nic : nic_state) (WRITABLE : 32 word -> bool) =
  RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM WRITABLE /\
  RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic WRITABLE /\
  RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic /\
  RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic`;

val _ = export_theory();
