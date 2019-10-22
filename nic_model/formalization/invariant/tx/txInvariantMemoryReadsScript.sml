open HolKernel Parse boolLib bossLib;
open CPPI_RAMTheory;
open tx_state_definitionsTheory;
open tx_bd_queueTheory;

val _ = new_theory "txInvariantMemoryReads";

(*
 * This file defines the parts of the transmission invariant the ensures that
 * the NIC can only address readable memory.
 *
 * Readable memory is specified by the undefined predicate READABLE.
 *)

(*
 * The NIC must only address readable memory:
 * -Start address: start + bufferoffset
 * -End address: start + bufferoffset + length - 1
 *
 * !pa. MEM pa [start + bufferoffset, start + bufferoffset + length) ==> READABLE pa
 *)

(*
 * Invariant implying that the buffer descriptor addresses readable memory.
 *)
val TX_INVARIANT_MEMORY_READABLE_BD_def = Define `
  TX_INVARIANT_MEMORY_READABLE_BD (bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) (READABLE : 32 word -> bool) =
  let bd = tx_read_bd bd_pa CPPI_RAM
  in
  (bd.sop ==> !pa. bd.bp + bd.bo <=+ pa /\ pa <=+ bd.bp + bd.bo + (bd.bl - 1w) ==> READABLE pa) /\
  (~bd.sop ==> !pa. bd.bp <=+ pa /\ pa <=+ bd.bp + (bd.bl - 1w) ==> READABLE pa)`;

(*
 * Invariant implying that the queue of transmission buffer descriptors
 * address only readable memory.
 *)
val TX_INVARIANT_MEMORY_READABLE_BD_QUEUE_def = Define `
  TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (q : 32 word list)
                                        (READABLE : 32 word -> bool)
                                        (CPPI_RAM : 13 word -> 8 word) =
  EVERY (\bd_pa. TX_INVARIANT_MEMORY_READABLE_BD bd_pa CPPI_RAM READABLE) q`;

(*
 * Invariant implying that if the transmission automaton is in the state
 * issue_next_memory_read_request, then there are bytes left to request.
 *)
val TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def = Define `
  TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE (nic : nic_state) =
  TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic
  ==>
  nic.tx.number_of_buffer_bytes_left_to_request >+ 0w`;

(*
 * Invariant implying that if there are bytes left to request, then this
 * address interval does not overflow.
 *)
val TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def = Define `
  TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE (nic : nic_state) =
  TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic \/
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic
  ==>
  (nic.tx.number_of_buffer_bytes_left_to_request >+ 0w
   ==>
   ~(nic.tx.pa_of_next_memory_buffer_byte + (nic.tx.number_of_buffer_bytes_left_to_request - 1w) <+ nic.tx.pa_of_next_memory_buffer_byte))`;

(*
 * Invariant implying that the transmission part of the NIC can only issue
 * memory read requests to readable memory.
 *)
val TX_INVARIANT_MEMORY_READABLE_STATE_def = Define `
  TX_INVARIANT_MEMORY_READABLE_STATE (nic : nic_state) (READABLE : 32 word -> bool) =
  TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic \/
  TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\ nic.tx.number_of_buffer_bytes_left_to_request >+ 0w
  ==>
  !pa.
  nic.tx.pa_of_next_memory_buffer_byte <=+ pa /\
  pa <=+ nic.tx.pa_of_next_memory_buffer_byte + (nic.tx.number_of_buffer_bytes_left_to_request - 1w)
  ==>
  READABLE pa`;

(*
 * Invariant of the transmission automaton implying the transmission part of the
 * NIC can only address readable memory, excluding undefined aspects.
 *
 * This invariant depends on the following state components:
 * -nic.regs.CPPI_RAM
 * -nic.tx.sop_bd_pa
 * -nic.tx.state
 * -nic.tx.pa_of_next_memory_buffer_byte
 * -nic.tx.number_of_buffer_bytes_left_to_request
 *)
val TX_INVARIANT_MEMORY_READABLE_def = Define `
  TX_INVARIANT_MEMORY_READABLE (nic : nic_state) (READABLE : 32 word -> bool) =
  TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM /\
  TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic /\
  TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic /\
  TX_INVARIANT_MEMORY_READABLE_STATE nic READABLE`;

val _ = export_theory();
