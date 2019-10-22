open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantMemoryWritesTheory;
open rxInvariantMemoryWritesRX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE_lemmasTheory;
open rx_transition_lemmasTheory;
open rx_transition_definitionsTheory;
open rxInvariantMemoryWritesRX_INVARIANTs_CURRENT_BUFFER_WRITABLE_NEXT_MEMORY_WRITE_PA_lemmasTheory;
open rx_transition_preserves_rx_invariant_well_definedTheory;
open rxTheory;
open rx_state_definitionsTheory;

val _ = new_theory "rx_transition_preserves_rx_invariant_and_only_writes_writable_memory";

(* Theorems of the form:
   !nic nic' WRITABLE.
   (nic' = (FST o rx_2issue_next_memory_write_request) nic) /\
   RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic /\
   RX_INVARIANT_MEMORY nic WRITABLE
   ==>
   RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE *)
val NIC_DELTA_RX_INVARIANT_IMP_WRITABLE_BD_QUEUE_lemmas =
  let fun create_goal lemma =
    let val (quantifiers, imp) = (strip_forall o concl) lemma in
    let val (conj1, conjr) = (dest_conj o #1 o dest_imp) imp in
    let val conj2 = (#1 o dest_conj) conjr in
    let val conj3 = ``RX_INVARIANT_MEMORY nic WRITABLE`` in
    let val ant = mk_conj (conj1, mk_conj (conj2, conj3)) in
    let val suc = ``RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE
                    (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE`` in
    let val new_imp = mk_imp (ant, suc) in
    let val goal = list_mk_forall (quantifiers, new_imp) in
      goal
    end end end end end end end end in
  let fun solve_goal lemma =
    let val rx_state_transition_state_application =
      (#1 o dest_conj o #2 o dest_conj o #1 o dest_imp o #2 o strip_forall o concl) lemma in
    let val rx_id =
      rxLib.rx_transition_state_application_to_rx_id
        rx_state_transition_state_application in
      REPEAT GEN_TAC THEN
      REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
      REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def]  THEN
      REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_def]  THEN
      DISCH_TAC THEN
      SPLIT_ASM_TAC THEN
      ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (rxLib.get_rx_conjunct NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_CONJ_lemmas rx_id))) THEN
      ASM_REWRITE_TAC []
    end end in
  let fun prove_goal lemma =
    prove (create_goal lemma, solve_goal lemma)
  in
    map prove_goal (CONJ_LIST 20 NIC_DELTA_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_CONJ_lemmas)
  end end end;

fun prove_memory_writable_bd_queue (rx_id : int) =
   ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id))) THEN
   ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``(nic', mr') = rx_transition nic v`` THEN
   ((RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
    PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) ORELSE
    (ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_FST_lemma)))) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC (List.nth (NIC_DELTA_RX_INVARIANT_IMP_WRITABLE_BD_QUEUE_lemmas, rx_id)) THEN
   TRY (EXISTS_TAC ``nic: nic_state``) THEN
   TRY (EXISTS_TAC ``env : environment``) THEN
   ASM_REWRITE_TAC [];

val rx_transition_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemma = store_thm (
  "rx_transition_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    RX_INVARIANT_MEMORY_WRITABLE_BD_QUEUE (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_state_lemmasTheory.RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id left_disjunct in
      ASM_CASES_TAC left_disjunct THENL
      [
       prove_memory_writable_bd_queue rx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_memory_writable_bd_queue 19);





(* Function used to prove the last three predicates of the memory invariant for each state. *)
fun prove_goal_with_current_state_and_lemmas (rx_id : int) (lemmas : thm list) =
  ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id))) THEN
  ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``(nic', mr') = rx_transition env nic`` THEN
  TRY (RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (List.nth (lemmas, rx_id)))) THEN
  ASM_REWRITE_TAC [];

(* Tactic used to prove the last three predicates of the memory invariant. *)
fun prove_goal_with_lemmas (lemmas : thm list) =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_state_lemmasTheory.RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id left_disjunct in
      ASM_CASES_TAC left_disjunct THENL
      [
       prove_goal_with_current_state_and_lemmas rx_id lemmas
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_goal_with_current_state_and_lemmas 19 lemmas;

val rx_transition_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma = store_thm (
  "rx_transition_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    RX_INVARIANT_CURRENT_BUFFER_WRITABLE nic' WRITABLE``,
  prove_goal_with_lemmas (CONJ_LIST 20 NIC_DELTA_PRESERVES_CURRENT_BUFFER_WRITABLE_CONJ_lemmas));

val rx_transition_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma = store_thm (
  "rx_transition_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES nic'``,
  prove_goal_with_lemmas (CONJ_LIST 20 NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_CONJ_lemmas));

val rx_transition_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma = store_thm (
  "rx_transition_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    RX_INVARIANT_NEXT_MEMORY_WRITE_PA_IN_BUFFER nic'``,
  prove_goal_with_lemmas (CONJ_LIST 20 NIC_DELTA_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_CONJ_lemmas));

val rx_transition_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_lemma = store_thm (
  "rx_transition_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    RX_INVARIANT_MEMORY_WRITABLE nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_MEMORY_WRITABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_CURRENT_BUFFER_WRITABLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_NEXT_MEMORY_WRITE_PA_EQ_BP_PLUS_NUMBER_OF_WRITTEN_BYTES_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_transition_PRESERVES_NEXT_MEMORY_WRITE_PA_IN_BUFFER_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_MEMORY_WRITABLE_def]);

val rx_transition_PRESERVES_RX_INVARIANT_MEMORY_lemma = store_thm (
  "rx_transition_PRESERVES_RX_INVARIANT_MEMORY_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE
    ==>
    RX_INVARIANT_MEMORY nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_PRESERVES_RX_INVARIANT_MEMORY_WRITABLE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_MEMORY nic WRITABLE`` RX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_PRESERVES_RX_INVARIANT_WELL_DEFINED_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_RX_INVARIANT_lemma",
  ``!nic env nic' mr' WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_INVARIANT nic WRITABLE
    ==>
    RX_INVARIANT nic' WRITABLE``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC rx_transition_PRESERVES_RX_INVARIANT_MEMORY_lemma THEN
  Q.EXISTS_TAC `nic` THEN
  Q.EXISTS_TAC `env` THEN
  Q.EXISTS_TAC `mr'` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_TRANSITION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val rx_transition_ISSUES_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "rx_transition_ISSUES_MEMORY_WRITE_REQUEST_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    IS_SOME mr'
    ==>
    ((nic', mr') = rx_2issue_next_memory_write_request nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_transition_def] THEN
  Cases_on `nic.rx.state` THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ, boolTheory.AND1_THM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
  RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val rx_transition_ISSUES_MEMORY_WRITE_REQUEST_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma = store_thm (
  "rx_transition_ISSUES_MEMORY_WRITE_REQUEST_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    IS_SOME mr'
    ==>
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_def] THEN
  REWRITE_TAC [rx_transition_def] THEN
  Cases_on `nic.rx.state` THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
  RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val rx_transition_WRITES_ONLY_WRITABLE_MEMORY_lemma = store_thm (
  "rx_transition_WRITES_ONLY_WRITABLE_MEMORY_lemma",
  ``!nic env nic' mr' WRITABLE.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_MEMORY nic WRITABLE /\
    IS_SOME mr'
    ==>
    WRITABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_ISSUES_MEMORY_WRITE_REQUEST_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_ISSUES_MEMORY_WRITE_REQUEST_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_MEMORY nic WRITABLE`` RX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [] (SPECL [``nic : nic_state``, ``nic' : nic_state``, ``mr' : memory_request option``, ``(THE mr').pa``, ``WRITABLE : bd_pa_type -> bool``] rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_RX_MEMORY_SUBINVARIANT_IMP_WRITE_WRITABLE_MEMORY_lemma))) THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_WRITES_ONLY_WRITABLE_MEMORY_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_WRITES_ONLY_WRITABLE_MEMORY_lemma",
  ``!nic env nic' mr' WRITABLE.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_INVARIANT nic WRITABLE /\
    IS_SOME mr'
    ==>
    WRITABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_WRITES_ONLY_WRITABLE_MEMORY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

