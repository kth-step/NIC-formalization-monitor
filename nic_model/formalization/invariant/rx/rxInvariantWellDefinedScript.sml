open HolKernel Parse boolLib bossLib;
open stateTheory;
open bd_queueTheory;
open rx_bd_queueTheory;
open it_state_definitionsTheory;
open rx_state_definitionsTheory;
open rx_transition_definitionsTheory;

(*
 * This file contains:
 * 1. The definition of the invariant for the reception automaton that ensures
 *    that the reception automaton never enters an undefined state.
 *
 * 2. Some general lemmas stating properties involving the predicates of the
 *    invariant.
 *)

val _ = new_theory "rxInvariantWellDefined";

val RX_INVARIANT_NOT_DEAD_def = Define `
  RX_INVARIANT_NOT_DEAD nic = ~nic.dead`;

(*
 * There exists a valid reception queue.
 *
 * Depends on the following state components:
 * -nic.rx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *)
val RX_INVARIANT_BD_QUEUE_FINITE_def = Define `
  RX_INVARIANT_BD_QUEUE_FINITE (nic : nic_state) =
  ?q. BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM`;

(*
 * The following expressions have the following meanings:
 * *rx_bd_queue nic: The smallest queue such that if the reception automaton
 *  writes a buffer descriptor, then that buffer descriptor is located at an
 *  address in the queue rx_bd_queue nic.
 * *rx_seen_bd_queue: The initial subqueue of rx_bd_queue whose buffer
 *  descriptors have been read by rx_1fetch_next_bd.
 * *rx_unseen_bd_queue nic: The trailing subqueue of rx_bd_queue following
 *  rx_seen_bd_queue of buffer descriptors that have not been read yet by
 *  rx_1fetch_next_bd.
 *
 * Formally:
 * ∃rx_seen_bd_queue. rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic.
 *
 * (~empty q) = (nic.rx.sop_bd_pa <> 0w)
 *
 * Queue Structure Invariant:
 * ?rx_seen_bd_queue. rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic
 *
 * Let q = rx_bd_queue nic.
 *
 * The following is desirable knowledge about which queues sop_bd_pa,
 * current_bd_pa, eop_bd_pa and ndp are members of:
 * Membership               sop_bd_pa         current_bd_pa     eop_bd_pa       ndp
 * rx_idle ∧ ¬empty q       unseen_bd_queue   unseen_bd_queue
 * rx_fetch_next_bd ∧ ¬sop  seen_bd_queue     unseen_bd_queue
 * _                        seen_bd_queue     seen_bd_queue     unseen_bd_queue
 * write_eop_buffer_length  seen_bd_queue     seen_bd_queue     seen_bd_queue   unseen_bd_queue
 * _                        seen_bd_queue     seen_bd_queue     seen_bd_queue   unseen_bd_queue
 * write_cp ∧ ¬empty q      unseen_bd_queue   unseen_bd_queue
 *
 * Queue Structure Invariant implies:
 * Membership             sop_bd_pa
 * idle ∧ ¬empty q        unseen_bd_pa      From definitions of rx_bd_queue and rx_unseen_bd_queue.
 * fetch_next_bd ∧ ¬sop   seen_bd_queue     From definitions of rx_bd_queue and rx_unseen_bd_queue
 *                                          and the assumption
 *                                          ¬sop (nic.rx.sop_bd_pa ≠ nic.rx.current_bd_pa).
 * _                      seen_bd_queue     With help from:
 *                                          -a) Invariant 1:
 *                                              state ≠ idle,fetch,write_cp
 *                                              ⇒
 *                                              nic.rx.current_bd.ndp =
 *                                              read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM
 *                                          -b) Prove MEM nic.rx.current_bd_pa rx_seen_bd_queue
 *                                              by means of a). By the definition of rx_bd_queue,
 *                                              sop_bd_pa is head of rx_bd_queue and seen.
 * write_cp ∧ ¬empty q    unseen_bd_queue   With help from:
 *                                          -a) Invariant 2:
 *                                              nic.rx.state = rx_idle \/
 *                                              nic.rx.state = rx_write_cp
 *                                              ==>
 *                                              nic.rx.current_bd_pa = nic.rx.sop_bd_pa
 *                                          -b) Invariant 3:
 *                                              nic.rx.state = rx_write_cp
 *                                              ==>
 *                                              nic.rx.current_bd_pa = nic.rx.current_bd.ndp
 *                                          -c) Use assumption write_cp ∧ ¬empty q, a) and b) to
 *                                              prove nic.rx.sop_bd_pa = nic.rx.current_bd.ndp and
 *                                              then use the definition of rx_unseen_bd_queue.
 *
 * Membership             current_bd_pa
 * idle ∧ ¬empty q        unseen_bd_queue   With help from:
 *                                          -a) Invariant 2:
 *                                              nic.rx.state = rx_idle \/
 *                                              nic.rx.state = rx_write_cp
 *                                              ==>
 *                                              nic.rx.current_bd_pa = nic.rx.sop_bd_pa
 *                                          -b) Use assumption idle ∧ ¬empty q and a) with the
 *                                              definition of rx_unseen_bd_queue.
 * fetch_next_bd ∧ ¬sop  unseen_bd_queue    Follows from the definition of rx_unseen_bd_queue.
 * _                     seen_bd_queue      With help from:
 *                                          -a) Invariant 1:
 *                                              state ≠ idle,fetch,write_cp
 *                                              ⇒
 *                                              nic.rx.current_bd.ndp =
 *                                              read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM
 *                                          -b) Invariant 4:
 *                                              state ≠ idle,write_cp
 *                                              ⇒
 *                                              MEM nic.rx.current_bd_pa rx_bd_queue nic
 *                                          -c) Use assumption _ and a) to prove that current_bd_pa
 *                                              is not in rx_unseen_bd_queue and then b.
 * write_cp ∧ ¬empty q   unseen_bd_queue    With help from:
 *                                          -a) Invariant 3:
 *                                              nic.rx.state = rx_write_cp
 *                                              ==>
 *                                              nic.rx.current_bd_pa = nic.rx.current_bd.ndp
 *                                          -b) Use assumtpion write_cp ∧ ¬empty q, a) and
 *                                              definition of rx_unseen_bd_queue.
 * 
 * Membership            eop_bd_pa
 * idle ∧ ¬empty q       Undefined
 * fetch_next_bd ∧ ¬sop  Undefined
 * _
 * write_eop_buffer_length seen_bd_queue    With help from:
 *                                          -a) Invariant 5:
 *                                          nic.rx.state = rx_write_eop_buffer_length ∨
 *                                          ... ∨
 *                                          nic.rx.state = rx_clear_sop_owner_and_hdp
 *                                          ⇒
 *                                          nic.rx.eop_bd_pa = nic.rx.current_bd_pa
 *                                          -b) and MEM current_bd_pa seen_bd_queue from above.
 * _                     seen_bd_queue      These states are treated as the previous case.
 * write_cp ∧ ¬empty q   Not intereseting
 *
 * Membership            ndp
 * idle ∧ ¬empty q       Undefined
 * fetch_next_bd ∧ ¬sop  Undefined
 * _                     unseen_bd_queue    Follows from the definition of rx_unseen_bd_queue.
 * write_cp ∧ ¬empty q
 *
 *
 *
 * Well-defined queue (only necessary for buffer descriptors to be processed;
 * unseen buffer descriptors): To ensure that the reception automaton never
 * enters a dead state, each buffer descriptor must be well-defined in the
 * queue starting from the following addresses in the following states:
 * *nic.rx.state = rx_idle: From SOP.
 * *nic.rx.state = rx_fetch_next_bd: From current_bd_pa.
 * *Other states: From current_bd.ndp
 *
 *
 * Depends on the following state components:
 * -nic.rx.state
 * -nic.rx.sop_bd_pa
 * -nic.rx.current_bd_pa
 * -nic.rx.current_bd.ndp
 * -nic.regs.CPPI_RAM
 *)

val RX_INVARIANT_BD_QUEUE_STRUCTURE_def = Define `
  RX_INVARIANT_BD_QUEUE_STRUCTURE (nic : nic_state) =
  ?rx_seen_bd_queue. rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic`;

(*
 * Invariant 1:
 * state ≠ idle,fetch,write_cp
 * ⇒
 * nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM
 *)
val RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def = Define `
  RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA (nic : nic_state) =
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic
  ==>
  (nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM)`;

(*
 * Invariant 2:
 * nic.rx.state = rx_idle /\ nic.it.state = initialized \/
 * nic.rx.state = rx_write_cp
 * ==>
 * nic.rx.current_bd_pa = nic.rx.sop_bd_pa
 *)
val RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def = Define `
  RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA (nic : nic_state) =
  (RX_STATE_IDLE nic /\ IT_STATE_INITIALIZED nic) \/
  RX_STATE_WRITE_CP nic
  ==>
  (nic.rx.current_bd_pa = nic.rx.sop_bd_pa)`;

(*
 * Invariant 3:
 * nic.rx.state = rx_write_cp
 * ==>
 * nic.rx.current_bd_pa = nic.rx.current_bd.ndp
 *)
val RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def = Define `
  RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP (nic : nic_state) =
  RX_STATE_WRITE_CP nic
  ==>
  (nic.rx.current_bd_pa = nic.rx.current_bd.ndp)`;

(*
 * Invariant 4:
 * state = ...
 * ⇒
 * MEM nic.rx.current_bd_pa rx_bd_queue nic
 *)
val RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def = Define `
  RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE (nic : nic_state) =
  RX_STATE_RECEIVE_FRAME nic \/
  RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic \/
  RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY nic
  ==>
  MEM nic.rx.current_bd_pa (rx_bd_queue nic)`;

(*
 * Invariant 5:
 * nic.rx.state = rx_write_eop_buffer_length ∨ ... ∨ nic.rx.state = rx_clear_sop_owner_and_hdp
 * ⇒
 * nic.rx.eop_bd_pa = nic.rx.current_bd_pa
 *)
val RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def = Define `
  RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA (nic : nic_state) =
  RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic
  ==>
  (nic.rx.eop_bd_pa = nic.rx.current_bd_pa)`;



(*
 * All invariants used to prove necessary properties about the queue structure.
 *)
val RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def = Define `
  RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT (nic : nic_state) =
  RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
  RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
  RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic /\
  RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
  RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic`;

(*
 * True if and only if there are no overlapping buffer descriptors in the
 * reception queue.
 *)
val RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def = Define `
  RX_INVARIANT_BD_QUEUE_NO_OVERLAP (q : 32 word list) = ~BD_LIST_OVERLAP q`;

(*
 * True if and only if each buffer descriptor location is well-defined.
 *)
val RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_def = Define `
  RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q = EVERY BD_LOCATION_DEFINED q`;

(*
 * True if and only if each buffer descriptor to process is well-defined.
 * Assumes that the RX_BUFFER_OFFSET register contains zero and for that reason
 * it does not matter whether a buffer descriptor will be a SOP or not.
 *)
val RX_INVARIANT_BD_WELL_DEFINED_def = Define `
  RX_INVARIANT_BD_WELL_DEFINED (bd : bd_data) =
  (bd.bo = 0w) /\
  bd.bl >+ 0w /\
  ~bd.sop /\ ~bd.eop /\ bd.own /\ ~bd.eoq /\ ~bd.pass_crc /\
  RX_BUFFER_IN_BBB_RAM bd 0w /\
  ~RX_BUFFER_OVERFLOW bd 0w`;
  
val RX_INVARIANT_BD_QUEUE_WELL_DEFINED_def = Define `
  RX_INVARIANT_BD_QUEUE_WELL_DEFINED (q : 32 word list) (CPPI_RAM : 13 word -> 8 word) =
  EVERY (\bd_pa. RX_INVARIANT_BD_WELL_DEFINED (rx_read_bd bd_pa CPPI_RAM)) q`;

(*
 * True if and only if the RX_BUFFER_OFFSET register contains zero.
 *
 * Depends on the following state components:
 * -nic.regs.RX_BUFFER_OFFSET
 *)
val RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def = Define `
  RX_INVARIANT_RX_BUFFER_OFFSET_ZERO (nic : nic_state) = (nic.regs.RX_BUFFER_OFFSET = 0w)`;

(*
 * The part of the invariant of the reception automaton ensuring that the
 * reception cannot cause the NIC to enter an undefined state.
 *)
val RX_INVARIANT_WELL_DEFINED_def = Define `
  RX_INVARIANT_WELL_DEFINED (nic : nic_state) =
  RX_INVARIANT_NOT_DEAD nic /\
  RX_INVARIANT_BD_QUEUE_FINITE nic /\
  RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
  RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
  RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
  RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
  RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
  RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic`;

val _ = export_theory();
