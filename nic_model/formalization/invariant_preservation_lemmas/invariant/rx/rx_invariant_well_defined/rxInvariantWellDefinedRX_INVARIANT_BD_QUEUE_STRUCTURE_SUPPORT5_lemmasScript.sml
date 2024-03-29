open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_state_definitionsTheory;
open rx_bd_queueTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT5_lemmas";

val NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic.
    ~RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

fun store_thm_rx_state_imp_bd_queue_structure_support5 (STATE : thm) (LEMMA : thm) (name : string) =
  let val ant = (#1 o dest_eq o #2 o dest_forall o concl) STATE
      val suc = ``RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic``
      val goal = mk_forall (``nic : nic_state``, mk_imp (ant, suc))
      val tactic =
        GEN_TAC THEN
        DISCH_TAC THEN
        MATCH_MP_TAC NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma THEN
        MATCH_MP_TAC LEMMA THEN
        ASM_REWRITE_TAC []
  in
    store_thm (name, goal, tactic)
  end;

val RX_STATE_IDLE_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_IDLE_def
  RX_STATE_IDLE_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_IDLE_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";

val RX_STATE_FETCH_NEXT_BD_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_FETCH_NEXT_BD_def
  RX_STATE_FETCH_NEXT_BD_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_FETCH_NEXT_BD_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";

val RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_WRITE_PACKET_ERROR_def
  RX_STATE_WRITE_PACKET_ERROR_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_WRITE_PACKET_ERROR_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";

val RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_WRITE_RX_VLAN_ENCAP_def
  RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";

val RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_WRITE_FROM_PORT_def
  RX_STATE_WRITE_FROM_PORT_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_WRITE_FROM_PORT_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";

val RX_STATE_WRITE_CP_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma =
  store_thm_rx_state_imp_bd_queue_structure_support5
  RX_STATE_WRITE_CP_def
  RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma
  "RX_STATE_WRITE_CP_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma";



val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_PRESERVES_CURRENT_BD_PA_EOP_BD_PA_IMP_BD_QUEUE_STRUCTURE_SUPPORT5_lemma",
  ``!nic nic'.
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

fun store_thm_rx_state_imp_write_cppi_ram_post_process (STATE : thm) (name : string) =
  let val ant = (#1 o dest_eq o #2 o dest_forall o concl) STATE
      val suc = ``RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic``
      val goal = mk_forall (``nic : nic_state``, mk_imp (ant, suc))
      val tactic =
        GEN_TAC THEN
        REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_EOP_OR_EOP_SOP_def, RX_STATE_WRITE_EOP_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_EOP_SOP_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA_def] THEN
        DISCH_TAC THEN
        ASM_REWRITE_TAC []
  in
    store_thm (name, goal, tactic)
  end

val RX_STATE_WRITE_EOP_BUFFER_LENGTH_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_EOP_BUFFER_LENGTH_def
  "RX_STATE_WRITE_EOP_BUFFER_LENGTH_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_SET_EOP_EOP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_SET_EOP_EOP_def
  "RX_STATE_SET_EOP_EOP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_def
  "RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_BUFFER_OFFSET_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_BUFFER_OFFSET_def
  "RX_STATE_WRITE_SOP_BUFFER_OFFSET_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_BUFFER_LENGTH_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_BUFFER_LENGTH_def
  "RX_STATE_WRITE_SOP_BUFFER_LENGTH_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_SET_SOP_SOP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_SET_SOP_SOP_def
  "RX_STATE_SET_SOP_SOP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_PASS_CRC_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_PASS_CRC_def
  "RX_STATE_WRITE_SOP_PASS_CRC_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_LONG_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_LONG_def
  "RX_STATE_WRITE_SOP_LONG_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_SHORT_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_SHORT_def
  "RX_STATE_WRITE_SOP_SHORT_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_MAC_CTL_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_MAC_CTL_def
  "RX_STATE_WRITE_SOP_MAC_CTL_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_WRITE_SOP_PACKET_LENGTH_def
  "RX_STATE_WRITE_SOP_PACKET_LENGTH_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_def
  "RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_write_cppi_ram_post_process
  RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def
  "RX_STATE_CLEAR_SOP_OWNER_AND_HDP_IMP_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val _ = export_theory();

