open HolKernel Parse boolLib bossLib;
open rx_state_definitionsTheory;
open rxInvariantWellDefinedTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT3_lemmas";

(* Given a theorem of a state definition, e.g. RX_STATE_FETCH_NEXT_BD_def,
   stores a theorem of the form:
   RX_STATE_FETCH_NEXT_BD nic
   ==>
   RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic

   Invoked as follows:
   store_thm_rx_state_imp_bd_queue_structure_support3 RX_STATE_FETCH_NEXT_BD_def "name_of_stored_theorem".
 *)
fun store_thm_rx_state_imp_bd_queue_structure_support3 (STATE : thm) (name : string) =
  let val ant = (#1 o dest_eq o #2 o dest_forall o concl) STATE
      val suc = (#1 o dest_eq o #2 o dest_forall o concl) RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def
      val goal = mk_forall (``nic : nic_state``, mk_imp (ant, suc))
      val tactic =
        GEN_TAC THEN
        REWRITE_TAC [STATE, RX_STATE_WRITE_CP_def, RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def] THEN
        DISCH_TAC THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
        (fn (asl : term list, conc : term) =>
           let val i1 = (#2 o dest_comb o #1 o dest_eq o #1 o dest_imp) conc
               val i2 = (#2 o dest_comb o #2 o dest_eq o #1 o dest_imp) conc
               val EQ_lemma = REWRITE_RULE [DECIDE ``^i1 < 20``, DECIDE ``^i2 < 20``, DECIDE ``^i1 <> ^i2``] (SPECL [i1, i2] stateTheory.num2rx_abstract_state_11)
           in
           REWRITE_TAC [EQ_lemma] (asl, conc)
           end)
  in
  store_thm (name, goal, tactic)
  end;

val RX_STATE_IDLE_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_IDLE_def
  "RX_STATE_IDLE_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_FETCH_NEXT_BD_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_FETCH_NEXT_BD_def
  "RX_STATE_FETCH_NEXT_BD_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_PACKET_ERROR_def
  "RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_RX_VLAN_ENCAP_def
  "RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_FROM_PORT_def
  "RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_EOP_BUFFER_LENGTH_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_EOP_BUFFER_LENGTH_def
  "RX_STATE_WRITE_EOP_BUFFER_LENGTH_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_SET_EOP_EOP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_SET_EOP_EOP_def
  "RX_STATE_SET_EOP_EOP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_def
  "RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_BUFFER_OFFSET_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_BUFFER_OFFSET_def
  "RX_STATE_WRITE_SOP_BUFFER_OFFSET_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_BUFFER_LENGTH_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_BUFFER_LENGTH_def
  "RX_STATE_WRITE_SOP_BUFFER_LENGTH_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_SET_SOP_SOP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_SET_SOP_SOP_def
  "RX_STATE_SET_SOP_SOP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_PASS_CRC_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_PASS_CRC_def
  "RX_STATE_WRITE_SOP_PASS_CRC_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_LONG_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_LONG_def
  "RX_STATE_WRITE_SOP_LONG_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_SHORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_SHORT_def
  "RX_STATE_WRITE_SOP_SHORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_MAC_CTL_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_MAC_CTL_def
  "RX_STATE_WRITE_SOP_MAC_CTL_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_WRITE_SOP_PACKET_LENGTH_def
  "RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_def
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support3
  RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def
  "RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_BD_QUEUE_STRUCTURE_SUPPORT3_lemma";

val _ = export_theory();

