open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open bd_queue_preservation_lemmasTheory;
open bd_listTheory;
open rx_write_defsTheory;
open rxInvariantWellDefinedLemmasTheory;
open rx_transition_lemmasTheory;
open rx_transition_definitionsTheory;
open rx_state_definitionsTheory;

val _ = new_theory "rx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUE";

fun create_eq_bds_goal_rx_id lemma =
  let val (quantifiers, predicate) = (strip_forall o concl) lemma in
  let val nic_delta =
    if is_imp predicate then
      (hd o #2 o strip_comb o #2 o dest_imp) predicate
    else
      (hd o #2 o strip_comb) predicate in
  let val rx_id = rxLib.rx_transition_function_to_rx_id nic_delta in
  let val rx_state_application = rxLib.rx_id_to_rx_transition_state_application rx_id in
  let val rx_invariant = ``RX_INVARIANT_WELL_DEFINED nic`` in
  let val bds_in_cppi_ram = ``BDs_IN_CPPI_RAM q`` in
  let val no_bd_list_overlap = ``NO_BD_LIST_OVERLAP q (rx_bd_queue nic)`` in
  let val ant = list_mk_conj [rx_state_application, rx_invariant, bds_in_cppi_ram, no_bd_list_overlap] in
  let val nic_delta_nic = mk_comb (nic_delta, ``nic : nic_state``) in
  let val nic_delta_nic_regs = mk_comb (``nic_state_regs``, nic_delta_nic) in
  let val nic_delta_nic_regs_cppi_ram = mk_comb (``nic_regs_CPPI_RAM``, nic_delta_nic_regs) in
  let val args = [``q : bd_pa_type list``, ``nic.regs.CPPI_RAM``, nic_delta_nic_regs_cppi_ram] in
  let val suc = list_mk_comb (``EQ_BDs``, args) in
  let val imp = mk_imp (ant, suc) in
  let val goal = list_mk_forall (quantifiers @ [``q : bd_pa_type list``], imp) in
    (goal, rx_id)
  end end end end end end end end end end end end end end end;

fun solve_eq_bds_goal (rx_id : int) = 
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (rxLib.get_rx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs rx_id)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  (fn g =>
   let val lemma = rxLib.get_rx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas rx_id in
     if (is_imp o #2 o strip_forall o concl) lemma then
       (MATCH_MP_TAC lemma THEN
        ASM_REWRITE_TAC []) g
     else
        ASM_REWRITE_TAC [lemma] g
   end);

(* Theorems of the form:
   |- ∀nic env q.
     RX_STATE_WRITE_CP nic ∧ RX_INVARIANT_WELL_DEFINED nic ∧
     BDs_IN_CPPI_RAM q ∧ NO_BD_LIST_OVERLAP q (rx_bd_queue nic) ⇒
     EQ_BDs q nic.regs.CPPI_RAM (rx_19write_cp env nic).regs.CPPI_RAM *)
val RX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUE_lemmas =
  let fun prove_lemma lemma =
    let val (goal, rx_id) = create_eq_bds_goal_rx_id lemma
    in
      prove (goal, solve_eq_bds_goal rx_id)
    end
  in
    map prove_lemma (CONJ_LIST 20 NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas)
  end;

fun prove_eq_bds (rx_id : int) =
 ASSUME_TAC ((UNDISCH o SPEC_ALL) (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id)) THEN
 ASM_RW_ASM_TAC ``rx_transition nic v = x`` ``(nic', mr') = rx_transition nic v`` THEN
 ((RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
   PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) ORELSE
  (ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_lemmasTheory.rx_2issue_next_memory_write_request_FST_lemma)))) THEN
 ASM_REWRITE_TAC [] THEN
 (let val rx_transition_function = rxLib.rx_id_to_rx_transition_function rx_id
  in
    if is_abs rx_transition_function then
      ONCE_REWRITE_TAC [(SYM o BETA_CONV o mk_comb) (rx_transition_function, ``nic : nic_state``)]
    else
      ALL_TAC
  end) THEN
 MATCH_MP_TAC (List.nth (RX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUE_lemmas, rx_id)) THEN
 ASM_REWRITE_TAC [];

val rx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUE_lemma = store_thm (
  "rx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_RX_BD_QUEUE_lemma",
  ``!nic env nic' mr' q.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT_WELL_DEFINED nic /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (rx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_state_lemmasTheory.RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_CASEs_lemma)) THEN
  RW_ASM_TAC ``P \/ Q`` (GSYM boolTheory.DISJ_ASSOC) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id left_disjunct in
      ASM_CASES_TAC left_disjunct THENL
      [
       prove_eq_bds rx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_eq_bds 19);

val _ = export_theory();
