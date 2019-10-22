open HolKernel Parse boolLib bossLib;
open stateTheory;
open bd_queueTheory;
open bd_listTheory;
open tx_bd_queueTheory;
open tx_state_definitionsTheory;
open txTheory;

val _ = new_theory "txInvariantWellDefined";

val TX_INVARIANT_NOT_DEAD_def = Define `
  TX_INVARIANT_NOT_DEAD nic = ~nic.dead`;

(*
 * True if and only if the transmission buffer descriptor queue is well-defined,
 * which basically means that it is finite. If the queue is infinite, then this
 * predicate would be false.
 *)
val TX_INVARIANT_BD_QUEUE_FINITE_def = Define `
  TX_INVARIANT_BD_QUEUE_FINITE (nic : nic_state) =
  ?q. BD_QUEUE q nic.tx.sop_bd_pa nic.regs.CPPI_RAM`;

(*
 * True if and only if there is no overlapping buffer descriptors in the
 * transmsision queue.
 *)
val TX_INVARIANT_BD_QUEUE_NO_OVERLAP_def = Define `
  TX_INVARIANT_BD_QUEUE_NO_OVERLAP (q : 32 word list) = ~BD_LIST_OVERLAP q`;

val TX_LINUX_BD_SOP_def = Define `
  TX_LINUX_BD_SOP bd_pa CPPI_RAM = (tx_read_bd bd_pa CPPI_RAM).sop`;

val TX_LINUX_BD_EOP_def = Define `
  TX_LINUX_BD_EOP bd_pa CPPI_RAM = (tx_read_bd bd_pa CPPI_RAM).eop`;

val TX_LINUX_BD_SOP_EOP_def = Define `
  TX_LINUX_BD_SOP_EOP bd_pa CPPI_RAM =
  TX_LINUX_BD_SOP bd_pa CPPI_RAM /\ TX_LINUX_BD_EOP bd_pa CPPI_RAM`;

(*
 * True if and only if every buffer descriptor in the queue is both a SOP and an
 * EOP. This statement reflects the way Linux uses buffer descriptors.
 *)
val TX_LINUX_BD_QUEUE_SOP_EOP_MATCH_def = Define `
  TX_LINUX_BD_QUEUE_SOP_EOP_MATCH q CPPI_RAM =
  EVERY (\bd_pa. TX_LINUX_BD_SOP_EOP bd_pa CPPI_RAM) q`;

(*
 * True if and only if the transmission buffer descriptor queue has a correct
 * matching of SOPs and EOPs. If a proof is desired where it is not assumed that
 * each buffer descriptor is both a SOP and an EOP, replace
 * LINUX_BD_QUEUE_SOP_EOP_MATCH with GENERAL_BD_QUEUE_SOP_EOP_MATCH.
 *)
val TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH_def = Define `
  TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (q : 32 word list) (CPPI_RAM : 13 word -> 8 word) =
  TX_LINUX_BD_QUEUE_SOP_EOP_MATCH q CPPI_RAM`;

(*
 * True if and only if each buffer descriptor location is well-defined.
 *)
val TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_def = Define `
  TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q = EVERY BD_LOCATION_DEFINED q`;

val NOT_TX_BD_QUEUE_EMPTY_def = Define `
  NOT_TX_BD_QUEUE_EMPTY nic = tx_bd_queue nic <> []`;

val TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY_def = Define `
  TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic =
  TX_STATE_NOT_BD_QUEUE_EMPTY nic
  ==>
  NOT_TX_BD_QUEUE_EMPTY nic`;

(*
 * The buffer descriptor at current_bd_pa needs to be a SOP in the state
 * write_cp when the queue is not empty (current_bd_pa <> 0), and does not need
 * to be a SOP when the state is clear_owner_and_hdp (since then the queue is
 * empty).
 *)
val TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE_def = Define `
  TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic =
  TX_STATE_NOT_BD_QUEUE_EMPTY nic
  ==>
  TX_EXPECTS_SOP_EQ_CURRENT_BD_SOP (tx_read_bd nic.tx.current_bd_pa nic.regs.CPPI_RAM) nic.tx`;

val TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH_def = Define `
  TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH bd_pa CPPI_RAM =
  ((tx_read_bd bd_pa CPPI_RAM).bl = (tx_read_bd bd_pa CPPI_RAM).pl)`;

val TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH_def = Define `
  TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH q CPPI_RAM =
  EVERY (\bd_pa. TX_INVARIANT_SOP_EOP_BD_CONSISTENT_SUM_BUFFER_LENGTH bd_pa CPPI_RAM) q`;

val TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW_def = Define `
  TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW bd_pa CPPI_RAM =
  (tx_read_bd bd_pa CPPI_RAM).bl <+ 2048w`;

val TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW_def = Define `
  TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW q CPPI_RAM =
  EVERY (\bd_pa. TX_INVARIANT_SOP_EOP_BD_NO_BUFFER_LENGTH_OVERFLOW bd_pa CPPI_RAM) q`;

val TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA_def = Define `
  TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA (nic : nic_state) =
  (nic.tx.current_bd_pa = nic.tx.sop_bd_pa)`;

val TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED_def = Define `
  TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED bd_pa CPPI_RAM =
  TX_CURRENT_BD_CONFIGURATION_WELL_DEFINED (tx_read_bd bd_pa CPPI_RAM)`;

val TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def = Define `
  TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED q CPPI_RAM =
  EVERY (\bd_pa. TX_INVARIANT_BD_CONFIGURATION_WELL_DEFINED bd_pa CPPI_RAM) q`;

val TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def = Define `
  TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED (nic : nic_state) =
  TX_STATE_IDLE_FETCH_NEXT_BD_WRITE_CP nic
  ==>
  TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED (tx_bd_queue nic) nic.regs.CPPI_RAM`;

val TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED_def = Define `
  TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED (nic : nic_state) =
  TX_STATE_MEMORY_REQUEST_CPPI_RAM_WRITE nic
  ==>
  TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED ((TL o tx_bd_queue) nic) nic.regs.CPPI_RAM`;

val TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE_def = Define `
  TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic =
  TX_INVARIANT_COMPLETE_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic /\
  TX_INVARIANT_TAIL_BD_QUEUE_CONFIGURATION_WELL_DEFINED nic`;

val TX_INVARIANT_CURRENT_BD_EOP_STATE_def = Define `
  TX_INVARIANT_CURRENT_BD_EOP_STATE (nic : nic_state) =
  TX_STATE_NOT_BD_QUEUE_EMPTY nic
  ==>
  nic.tx.current_bd.eop`;

(*
 * This invariant is necessary when post_process sets current_bd_pa and
 * sop_bd_pa to nic.tx.current_bd.ndp. The reason is that it must be guaranteed
 * that the next descriptor pointer does not point to the current head of the
 * queue. Since post_process clears the ownership bit, the subinvariant
 * TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE is breaked if the head
 * of the queue is not advanced.
 *
 * Also, it is not desired that the succedent of the invariant is true if the
 * software extends the queue. That is, software writes the next descriptor
 * pointer of the last buffer descriptor in the queue, thereby potentially
 * breaking the equality since the next descriptor pointer will most likely not
 * be equal to zero. Therefore, the conjunct nic.tx.current_bd.ndp <> 0w is
 * in the antecedent.
 *)
val BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE_def = Define `
  BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic =
  (TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic \/
   TX_STATE_PROCESS_MEMORY_READ_REPLY nic \/
   TX_STATE_POST_PROCESS nic) /\
  nic.tx.current_bd.ndp <> 0w`;

val CURRENT_BD_NDP_EQ_CPPI_RAM_NDP_def = Define `
  CURRENT_BD_NDP_EQ_CPPI_RAM_NDP nic =
  (nic.tx.current_bd.ndp = read_ndp nic.tx.current_bd_pa nic.regs.CPPI_RAM)`;

val TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE_def = Define `
  TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic =
  BD_QUEUE_ADVANCEMENT_DEPENDS_ON_NONZERO_NDP_STATE nic
  ==>
  CURRENT_BD_NDP_EQ_CPPI_RAM_NDP nic`;

(*
 * The internal data structure storing the currently processed buffer descriptor
 * does not need to satisfy any property in the states idle (since the
 * transmission automaton does not process any buffer descriptor in this state)
 * and fetch_next_bd (since a new buffer descriptor will be read in that state).
 *)
val TX_INVARIANT_CURRENT_BD_STATE_def = Define `
  TX_INVARIANT_CURRENT_BD_STATE nic =
  TX_INVARIANT_CURRENT_BD_EOP_STATE nic /\
  TX_INVARIANT_CURRENT_BD_NONZERO_NDP_EQ_CURRENT_BD_PA_NDP_STATE nic`;

(*
 * Current version of the invariant for the transmission automaton for
 * preventing the NIC model to enter a dead state.
 *
 * TX_INVARIANT_WELL_DEFINED shall be proved to be preserved by each transition
 * that the transmission automaton can perform.
 *
 *
 * TX_INVARIANT_WELL_DEFINED depends on the following state components:
 * -nic.dead
 * -nic.tx.current_bd_pa
 * -nic.tx.sop_bd_pa
 * -nic.tx.expects_sop
 * -nic.tx.current_bd.eop
 * -nic.tx.current_bd.ndp
 * -nic.tx.state
 * -nic.regs.CPPI_RAM
 *
 * Since TX_INVARIANT_WELL_DEFINED is defined in terms of the following
 * predicates, where their arguments have also beed considered.
 *
 * TX_INVARIANT_WELL_DEFINED:
 * -nic.dead
 *
 * TX_INVARIANT_BD_QUEUE_FINITE:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_BD_QUEUE_NO_OVERLAP:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_BD_QUEUE_NOT_EMPTY_STATE_def:
 * -nic.tx.state
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE:
 * -nic.tx.state
 * -nic.tx.expects_sop
 * -nic.tx.current_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 *
 * TX_INVARIANT_BD_QUEUE_CONFIGRURATION_WELL_DEFINED_STATE:
 * -nic.tx.sop_bd_pa
 * -nic.regs.CPPI_RAM
 * -nic.tx.state
 *
 * TX_INVARIANT_CURRENT_BD_STATE:
 * -nic.tx.current_bd.eop
 * -nic.tx.current_bd.ndp
 * -nic.tx.state
 * -nic.regs.CPPI_RAM
 * -nic.tx.current_bd_pa
 *)
val TX_INVARIANT_WELL_DEFINED_def = Define `
  TX_INVARIANT_WELL_DEFINED (nic : nic_state) =
  TX_INVARIANT_NOT_DEAD nic /\
  TX_INVARIANT_BD_QUEUE_FINITE nic /\
  TX_INVARIANT_BD_QUEUE_NO_OVERLAP (tx_bd_queue nic) /\
  TX_INVARIANT_BD_QUEUE_SOP_EOP_MATCH (tx_bd_queue nic) nic.regs.CPPI_RAM /\

  TX_INVARIANT_TX_STATE_NOT_BD_QUEUE_EMPTY nic /\
  TX_INVARIANT_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\

  TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (tx_bd_queue nic) /\

  TX_INVARIANT_EXPECTS_SOP_EQ_CURRENT_BD_PA_SOP_STATE nic /\

  TX_INVARIANT_SOP_EOP_BD_QUEUE_NO_BUFFER_LENGTH_OVERFLOW (tx_bd_queue nic) nic.regs.CPPI_RAM /\
  TX_INVARIANT_SOP_EOP_BD_QUEUE_CONSISTENT_SUM_BUFFER_LENGTH (tx_bd_queue nic) nic.regs.CPPI_RAM /\

  TX_INVARIANT_BD_QUEUE_CONFIGURATION_WELL_DEFINED_STATE nic /\

  TX_INVARIANT_CURRENT_BD_STATE nic`;

val _ = export_theory();
