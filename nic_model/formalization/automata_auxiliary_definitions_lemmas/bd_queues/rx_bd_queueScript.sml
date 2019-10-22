open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open bd_queueTheory;
open rx_state_definitionsTheory;
open bd_queue_preservation_lemmasTheory;
open bdTheory;
open CPPI_RAMTheory;
open bd_listTheory;

val _ = new_theory "rx_bd_queue";

(*
 * If the reception automaton performs a write to a buffer descriptor, then that
 * buffer descriptor is located in rx_bd_queue.
 *)
val rx_bd_queue_def = Define `rx_bd_queue (nic : nic_state) =
  bd_queue nic.rx.sop_bd_pa nic.regs.CPPI_RAM`;

val RX_BD_QUEUE_IMP_rx_bd_queue_lemma = store_thm (
  "RX_BD_QUEUE_IMP_rx_bd_queue_lemma",
  ``!nic q.
    BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM
    ==>
    (rx_bd_queue nic = q)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [rx_bd_queue_def] THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma = store_thm (
  "RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma",
  ``!nic q.
    BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM
    ==>
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [rx_bd_queue_def] THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

(*
 * The queue of buffer descriptors that the reception automaton has not fetched
 * yet.
 *)
val rx_unseen_bd_queue_def = Define `
  rx_unseen_bd_queue (nic : nic_state) =
  case nic.rx.state of
    | rx_idle => bd_queue nic.rx.sop_bd_pa nic.regs.CPPI_RAM
    | rx_fetch_next_bd => bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM
    | rx_write_cp => bd_queue nic.rx.sop_bd_pa nic.regs.CPPI_RAM
    | _ => bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM`;

val RX_idle_IMP_unseen_bd_queue_EQ_bd_queue_lemma = store_thm (
  "RX_idle_IMP_unseen_bd_queue_EQ_bd_queue_lemma",
  ``!nic.
    RX_STATE_IDLE nic
    ==>
    (rx_unseen_bd_queue nic = rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def, stateTheory.rx_abstract_state_case_def, rx_bd_queue_def]);

val RX_STATE_IDLE_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_SOP_BD_PA_lemma = store_thm (
  "RX_STATE_IDLE_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_SOP_BD_PA_lemma",
  ``!nic.
    RX_STATE_IDLE nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.sop_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [GSYM rx_bd_queue_def] THEN
  REWRITE_TAC [RX_idle_IMP_unseen_bd_queue_EQ_bd_queue_lemma]);

val RX_write_cp_IMP_unseen_bd_queue_EQ_bd_queue_lemma = store_thm (
  "RX_write_cp_IMP_unseen_bd_queue_EQ_bd_queue_lemma",
  ``!nic.
    RX_STATE_WRITE_CP nic
    ==>
    (rx_unseen_bd_queue nic = rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def, stateTheory.rx_abstract_state_case_def, rx_bd_queue_def]);

val RX_STATE_WRITE_CP_IMP_BD_QUEUE_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CP_IMP_BD_QUEUE_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_WRITE_CP nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.sop_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  REWRITE_TAC [rx_unseen_bd_queue_def] THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def]);

val RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma",
  ``!nic.
    RX_STATE_FETCH_NEXT_BD nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_FETCH_NEXT_BD_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def, stateTheory.rx_abstract_state_case_def]);

(* Used to prove theorems about states of the reception automaton.
 *
 * Rewrites the goal with a theorem of the form:
 * num2rx_abstract_state i1 <> num2rx_abstract_state i2
 *)
fun distinct_rx_abstract_state_indexes_imp_distinct_states_tactic (i1 : int) (i2 : int) (asl : term list, conc : term) =
  let val ti1 = numSyntax.term_of_int i1
      val ti2 = numSyntax.term_of_int i2
  in
  let val equivalence = REWRITE_RULE [DECIDE ``^ti1 < 20``, DECIDE ``^ti2 < 20``] (SPECL [ti1, ti2] stateTheory.num2rx_abstract_state_11)
  in
  REWRITE_TAC [REWRITE_RULE [DECIDE ``^ti1 <> ^ti2``] equivalence] (asl, conc)
  end
  end;

(* Used to prove theorems about states of the reception automaton.
 *
 * Rewrites the current goal with theorems of the form:
 * num2rx_abstract_state i <> num2rx_abstract_state j, start <= j <= stop.
 *)
fun distinct_rx_abstract_state_indexes_interval_tactic (i : int) (start : int) (stop : int) (asl : term list, conc : term) =
  if start = stop then
    distinct_rx_abstract_state_indexes_imp_distinct_states_tactic i start (asl, conc)
  else
    (distinct_rx_abstract_state_indexes_imp_distinct_states_tactic i start THEN
     distinct_rx_abstract_state_indexes_interval_tactic i (start + 1) stop) (asl, conc);

val RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma = store_thm (
  "RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    (rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_PACKET_ERROR_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_RX_VLAN_ENCAP_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_FROM_PORT_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_EOP_OR_EOP_SOP_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_EOP_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_EOP_BUFFER_LENGTH_def] THEN
  REWRITE_TAC [RX_STATE_SET_EOP_EOP_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_EOP_SOP_def] THEN
  REWRITE_TAC [RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_BUFFER_OFFSET_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_BUFFER_LENGTH_def] THEN
  REWRITE_TAC [RX_STATE_SET_SOP_SOP_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_PASS_CRC_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_LONG_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_SHORT_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_MAC_CTL_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_PACKET_LENGTH_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA_def] THEN
  REWRITE_TAC [RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_def] THEN
  REWRITE_TAC [RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def] THEN
  REWRITE_TAC [rx_unseen_bd_queue_def] THEN
  Cases_on `nic.rx.state` THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
  ASM_REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THENL
  [
   distinct_rx_abstract_state_indexes_interval_tactic 0 2 18
   ,
   distinct_rx_abstract_state_indexes_interval_tactic 1 2 18
   ,
   distinct_rx_abstract_state_indexes_interval_tactic 19 2 18
  ]);

(* Given a theorem of a state definition, e.g. RX_STATE_FETCH_NEXT_BD_def,
   stores a theorem of the form:
   RX_STATE_FETCH_NEXT_BD nic
   ==>
   ~RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic

   Invoked as follows:
   store_thm_rx_state_imp_bd_queue_structure_support5 RX_STATE_FETCH_NEXT_BD_def "name_of_stored_theorem".
 *)
fun store_thm_rx_state_imp_not_write_cppi_ram_post_process (STATE : thm) (name : string) =
  let val ant = (#1 o dest_eq o #2 o dest_forall o concl) STATE
      val suc = mk_neg ((#1 o dest_eq o #2 o dest_forall o concl) RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_def)
      val goal = mk_forall (``nic : nic_state``, mk_imp (ant, suc))
      val tactic =
        GEN_TAC THEN
        REWRITE_TAC [STATE, RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_EOP_OR_EOP_SOP_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_EOP_def, RX_STATE_WRITE_EOP_SOP_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_EOP_BUFFER_LENGTH_def, RX_STATE_SET_EOP_EOP_def] THEN
        REWRITE_TAC [RX_STATE_SET_EOP_EOQ_OR_WRITE_SOP_BUFFER_OFFSET_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_BUFFER_OFFSET_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_BUFFER_LENGTH_def, RX_STATE_SET_SOP_SOP_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_PASS_CRC_def, RX_STATE_WRITE_SOP_LONG_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_SHORT_def, RX_STATE_WRITE_SOP_MAC_CTL_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_PACKET_LENGTH_def] THEN
        REWRITE_TAC [RX_STATE_WRITE_SOP_EOP_AND_WRITE_RX_SOP_BD_PA_def] THEN
        REWRITE_TAC [RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_def] THEN
        REWRITE_TAC [RX_STATE_CLEAR_SOP_OWNER_AND_HDP_def] THEN
        REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
        REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
        (fn (asl, conc) =>
           let val i = (numSyntax.int_of_term o #2 o dest_comb o #2 o dest_eq o #1 o dest_imp) conc
           in
           (DISCH_TAC THEN
            ASM_REWRITE_TAC [] THEN
            distinct_rx_abstract_state_indexes_interval_tactic i 6 18) (asl, conc)
           end)
  in
  store_thm (name, goal, tactic)
  end;

val RX_STATE_IDLE_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_IDLE_def
  "RX_STATE_IDLE_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_FETCH_NEXT_BD_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_FETCH_NEXT_BD_def
  "RX_STATE_FETCH_NEXT_BD_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_PACKET_ERROR_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_WRITE_PACKET_ERROR_def
  "RX_STATE_WRITE_PACKET_ERROR_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_WRITE_RX_VLAN_ENCAP_def
  "RX_STATE_WRITE_RX_VLAN_ENCAP_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_FROM_PORT_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_WRITE_FROM_PORT_def
  "RX_STATE_WRITE_FROM_PORT_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";

val RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma =
  store_thm_rx_state_imp_not_write_cppi_ram_post_process
  RX_STATE_WRITE_CP_def
  "RX_STATE_WRITE_CP_IMP_NOT_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma";



val RX_fetch_next_bd_BD_QUEUE_CURRENT_BD_PA_IMP_BD_QUEUE_rx_unseen_bd_queue_lemma = store_thm (
  "RX_fetch_next_bd_BD_QUEUE_CURRENT_BD_PA_IMP_BD_QUEUE_rx_unseen_bd_queue_lemma",
  ``!q nic.
    RX_STATE_FETCH_NEXT_BD nic /\
    BD_QUEUE q nic.rx.current_bd_pa nic.regs.CPPI_RAM
    ==>
    BD_QUEUE (rx_unseen_bd_queue nic) nic.rx.current_bd_pa nic.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q nic.rx.current_bd_pa nic.regs.CPPI_RAM`` BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma THEN
  ASSUME_TAC (GSYM (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma))) THEN
  ASM_RW_ASM_TAC ``bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM = rx_unseen_bd_queue nic`` ``BD_QUEUE (bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.rx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue bd_pa.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    MEM bd_pa rx_seen_bd_queue /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    ~MEM bd_pa (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``q = q' ++ q''`` ``BD_QUEUE q a m`` THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q a m`` BD_QUEUE_ALL_DISTINCT_lemma THEN
  RW_ASM_TAC ``ALL_DISTINCT q`` listTheory.ALL_DISTINCT_APPEND THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : 32 word`` thm))) THEN
  ASM_REWRITE_TAC []);






val RX_BD_QUEUE_NEXT_SOP_BD_PA_MEM_UNSEEN_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_NEXT_SOP_BD_PA_MEM_UNSEEN_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma",
  ``!nic nic'.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic'.regs.CPPI_RAM /\
    (?rx_seen_bd_queue. (rx_bd_queue nic) = rx_seen_bd_queue ++ rx_unseen_bd_queue nic) /\
    MEM nic'.rx.sop_bd_pa (rx_unseen_bd_queue nic)
    ==>
    BD_QUEUE (rx_bd_queue nic') nic'.rx.sop_bd_pa nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (SPECL [``nic'.rx.sop_bd_pa``, ``rx_seen_bd_queue : bd_pa_type list``, ``rx_unseen_bd_queue nic``] (GSYM (INST_TYPE [``: 'a``|-> ``: bd_pa_type``] listTheory.MEM_APPEND))) THEN
  ASM_RW_ASM_TAC ``MEM a q`` ``P = Q`` THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_RW_ASM_TAC ``x = y`` ``MEM a q`` THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``nic'.rx.sop_bd_pa``, ``nic.rx.sop_bd_pa``, ``nic'.regs.CPPI_RAM``] MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_TAC RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);


val EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma = store_thm (
  "EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma",
  ``!nic nic'.
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_bd_queue_def]);

val RX_BD_QUEUE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma = store_thm (
  "RX_BD_QUEUE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma",
  ``!nic nic'.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [rx_bd_queue_def] THEN
  MATCH_MP_TAC BD_QUEUE_EQ_BDs_IMP_EQ_BD_QUEUEs_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);

val RX_UNSEEN_BD_QUEUE_DEP_lemma = store_thm (
  "RX_UNSEEN_BD_QUEUE_DEP_lemma",
  ``!nic nic'.
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_unseen_bd_queue_def]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_CURRENT_BD_NDP_EQ_CPPI_RAM_EQ_IMP_RX_UNSEEN_BD_QUEUE_EQ_lemma = store_thm (
 "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_CURRENT_BD_NDP_EQ_CPPI_RAM_EQ_IMP_RX_UNSEEN_BD_QUEUE_EQ_lemma",
  ``!nic nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic' /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASM_REWRITE_TAC []);


val rx_read_bd_ndp_EQ_read_ndp_lemma = store_thm (
  "rx_read_bd_ndp_EQ_read_ndp_lemma",
  ``!bd_pa CPPI_RAM. (rx_read_bd bd_pa CPPI_RAM).ndp = read_ndp bd_pa CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_read_bd_def, read_ndp_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  ONCE_REWRITE_TAC [GSYM CPPI_RAMTheory.bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [CPPI_RAMTheory.bd_data_fn_updates] THEN
  REWRITE_TAC [combinTheory.K_THM] THEN
  REWRITE_TAC [CPPI_RAMTheory.bd_data_ndp]);

val BD_QUEUE_SAME_Q_IMP_EQ_RX_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_SAME_Q_IMP_EQ_RX_BD_QUEUE_lemma",
  ``!q nic nic'.
    BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BD_QUEUE q nic'.rx.sop_bd_pa nic'.regs.CPPI_RAM
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_BD_QUEUE_IMP_rx_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic' : nic_state``, ``q : 32 word list``] RX_BD_QUEUE_IMP_rx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);




val NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def = Define `
  NIC_DELTA_PRESERVES_RX_SOP_BD_PA (nic_delta : nic_state -> nic_state) (nic : nic_state) =
  ((nic_delta nic).rx.sop_bd_pa = nic.rx.sop_bd_pa)`;

val NIC_DELTA_PRESERVES_RX_BD_QUEUE_def = Define `
  NIC_DELTA_PRESERVES_RX_BD_QUEUE (nic_delta : nic_state -> nic_state) (nic : nic_state) =
  (rx_bd_queue (nic_delta nic) = rx_bd_queue nic)`;

val NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def = Define `
  NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE (nic_delta : nic_state -> nic_state) (nic : nic_state) =
  (rx_unseen_bd_queue (nic_delta nic) = rx_unseen_bd_queue nic)`;

val NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_def = Define `
  NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE nic_delta nic =
  ?q. rx_unseen_bd_queue nic = q ++ (rx_unseen_bd_queue (nic_delta nic))`;

val NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_def = Define `
  NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic =
  IN_LIST1_IMP_IN_LIST2 (rx_unseen_bd_queue (nic_delta nic)) (rx_unseen_bd_queue nic)`;

val NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_REWRITE_TAC [IN_SUFFIX_IMP_IN_LIST_lemma]);

val NIC_DELTA_SHRINKS_OR_PRESERVES_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_SHRINKS_OR_PRESERVES_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic.
    NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE nic_delta nic \/
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  Cases_on `NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE nic_delta nic` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL NIC_DELTA_SHRINKS_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_IMP_NOT_EXPANDS_RX_UNSEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE_def = Define `
  NIC_DELTA_NOT_EXPANDS_RX_BD_QUEUE (nic_delta : nic_delta_type) (nic : nic_state) =
  NIC_DELTA_NOT_EXPANDS_BD_QUEUE nic_delta nic nic.rx.sop_bd_pa (nic_delta nic).rx.sop_bd_pa`;

val NIC_DELTA_CLEARS_RX_SOP_BD_PA_def = Define `
  NIC_DELTA_CLEARS_RX_SOP_BD_PA (nic_delta : nic_delta_type) (nic : nic_state) = 
  ((nic_delta nic).rx.sop_bd_pa = 0w)`;

val NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def = Define `
  NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA (nic_delta : nic_state -> nic_state) (nic : nic_state) =
  ((nic_delta nic).rx.current_bd_pa = nic.rx.current_bd_pa)`;

val NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def = Define `
  NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP (nic_delta : nic_delta_type) nic =
  ((nic_delta nic).rx.current_bd.ndp = nic.rx.current_bd.ndp)`;

val NIC_DELTA_SETS_RX_SOP_BD_PA_TO_NDP_def = Define `
  NIC_DELTA_SETS_RX_SOP_BD_PA_TO_NDP (nic_delta : nic_delta_type) nic =
  ((nic_delta nic).rx.sop_bd_pa = nic.rx.current_bd.ndp)`;

val NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_def = Define `
  NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA (nic_delta : nic_delta_type) (nic : nic_state) =
  ((nic_delta nic).rx.current_bd_pa = nic.rx.current_bd.ndp)`;

val NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def = Define `
  NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA (nic_delta : nic_delta_type) (nic : nic_state) =
  ((nic_delta nic).rx.sop_bd_pa = nic.rx.current_bd.ndp)`;

val NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def = Define `
  NIC_DELTA_PRESERVES_OR_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic =
  NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic \/
  NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic`;

val RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma = store_thm (
  "RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma",
  ``!nic_delta nic q cppi_ram_write_step_bd_pas.
    BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q
    ==>
    BD_QUEUE q (nic_delta nic).rx.sop_bd_pa (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC ``nic.rx.sop_bd_pa`` (GEN ``start_bd_pa : bd_pa_type`` (SPEC_ALL NIC_DELTA_PRESERVES_BD_QUEUE_lemma)))) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def THEN
  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_STEP_BD_PAs_RX_SOP_EOP_CURRENT_BD_PA_def = Define `
  CPPI_RAM_WRITE_STEP_BD_PAs_RX_SOP_EOP_CURRENT_BD_PA (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type) (nic : nic_state) =
  !bd_pa.
  MEM bd_pa (MAP SND cppi_ram_write_step_bd_pas)
  ==>
  (bd_pa = nic.rx.sop_bd_pa) \/
  (bd_pa = nic.rx.eop_bd_pa) \/
  (bd_pa = nic.rx.current_bd_pa)`;











(*Start of definitions for writing nic.rx.current_bd_pa, nic.rx.eop_bd_pa and nic.rx.sop_bd_pa*)

(**Start of definitions regarding CPPI_RAM writes at current_bd_pa**)
val CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type) (nic : nic_state) =
  IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) [nic.rx.current_bd_pa]`;

val RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA_def = Define `
  RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA nic cppi_ram_write_step_bd_pas =
  RX_STATE_WRITE_CURRENT_BD_PA nic /\
  CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA cppi_ram_write_step_bd_pas nic`;
(**End of definitions regarding CPPI_RAM writes at current_bd_pa**)

(**Start of definitions regarding CPPI_RAM writes at eop_bd_pa**)
val CPPI_RAM_WRITE_STEPs_WRITE_EOP_BD_PA_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_EOP_BD_PA (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type) (nic : nic_state) =
  IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) [nic.rx.eop_bd_pa]`;

val RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA_def = Define `
  RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA nic cppi_ram_write_step_bd_pas =
  RX_STATE_WRITE_EOP nic /\
  CPPI_RAM_WRITE_STEPs_WRITE_EOP_BD_PA cppi_ram_write_step_bd_pas nic`;
(**End of definitions regarding CPPI_RAM writes at eop_bd_pa**)

(**Start of definitions regarding CPPI_RAM writes at eop_bd_pa and sop_bd_pa**)
val CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type) (nic : nic_state) =
  IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) [nic.rx.eop_bd_pa; nic.rx.sop_bd_pa]`;

val RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_def = Define `
  RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas =
  RX_STATE_WRITE_EOP_SOP nic /\
  CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA cppi_ram_write_step_bd_pas nic`;

val RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_def = Define `
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas =
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP nic /\
  CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA cppi_ram_write_step_bd_pas nic`;

(**End of definitions regarding CPPI_RAM writes at eop_bd_pa and sop_bd_pa**)

(**Start of definitions regarding CPPI_RAM writes at sop_bd_pa**)
val CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type) (nic : nic_state) =
  IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) [nic.rx.sop_bd_pa]`;

val RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_def = Define `
  RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA nic cppi_ram_write_step_bd_pas =
  RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA nic /\
  CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA cppi_ram_write_step_bd_pas nic`;
(**End of definitions regarding CPPI_RAM writes at sop_bd_pa**)

(*For functions writing CURRENT_BD_PA, EOP_BD_PA, EOP_BD_PA AND SOP_BD_PA, OR SOP_BD_PA. *)
val RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_def = Define `
  RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA nic cppi_ram_write_step_bd_pas =
  RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA nic cppi_ram_write_step_bd_pas \/
  RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA nic cppi_ram_write_step_bd_pas \/
  RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas \/
  RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA nic cppi_ram_write_step_bd_pas \/
  RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas`;

(*End of definitions for writing nic.rx.current_bd_pa, nic.rx.eop_bd_pa and nic.rx.sop_bd_pa*)


val BD_PAs_IN_RX_BD_QUEUE_def = Define `
  BD_PAs_IN_RX_BD_QUEUE bd_pas nic =
  EVERY (\bd_pa. MEM bd_pa (rx_bd_queue nic)) bd_pas`;

val NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def = Define `
  NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE bd_pas nic =
  EVERY (\bd_pa. ~MEM bd_pa (rx_unseen_bd_queue nic)) bd_pas`;

val BD_PAs_IN_RX_SEEN_BD_QUEUE_def = Define `
  BD_PAs_IN_RX_SEEN_BD_QUEUE bd_pas nic =
  BD_PAs_IN_RX_BD_QUEUE bd_pas nic /\
  NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE bd_pas nic`;

val EMPTY_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "EMPTY_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic. BD_PAs_IN_RX_SEEN_BD_QUEUE [] nic``,
  GEN_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [BD_PAs_IN_RX_BD_QUEUE_def] THEN
  REWRITE_TAC [NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF]);

val _ = export_theory();
