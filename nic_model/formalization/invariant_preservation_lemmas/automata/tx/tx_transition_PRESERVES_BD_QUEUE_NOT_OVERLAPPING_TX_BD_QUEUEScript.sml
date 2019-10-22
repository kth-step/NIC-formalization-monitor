open HolKernel Parse boolLib bossLib;
open helperTactics;
open txInvariantWellDefinedTheory;
open bd_queue_preservation_lemmasTheory;
open bd_listTheory;
open tx_write_defsTheory;
open tx_invariant_well_defined_lemmasTheory;
open tx_transition_lemmasTheory;
open tx_transition_definitionsTheory;

val _ = new_theory "tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE";

(* Creates a pair consisting of a term of the form:
   ``!nic env q.
     TX_STATE_WRITE_CP nic ∧ TX_INVARIANT_WELL_DEFINED nic ∧
     BDs_IN_CPPI_RAM q ∧ NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
     ==>
     EQ_BDs q nic.regs.CPPI_RAM (tx_6write_cp env nic).regs.CPPI_RAM``

   and the id number of the current transition function. *)
fun create_eq_bds_goal_tx_id lemma =
  let val (quantifiers, predicate) = (strip_forall o concl) lemma in
  let val nic_delta =
    if is_imp predicate then
      (hd o #2 o strip_comb o #2 o dest_imp) predicate
    else
      (hd o #2 o strip_comb) predicate in
  let val tx_id = txLib.tx_transition_function_to_tx_id nic_delta in
  let val tx_state_application = txLib.tx_id_to_tx_transition_state_application tx_id in
  let val tx_invariant = ``TX_INVARIANT_WELL_DEFINED nic`` in
  let val bds_in_cppi_ram = ``BDs_IN_CPPI_RAM q`` in
  let val no_bd_list_overlap = ``NO_BD_LIST_OVERLAP q (tx_bd_queue nic)`` in
  let val ant = list_mk_conj [tx_state_application, tx_invariant, bds_in_cppi_ram, no_bd_list_overlap] in
  let val nic_delta_nic = mk_comb (nic_delta, ``nic : nic_state``) in
  let val nic_delta_nic_regs = mk_comb (``nic_state_regs``, nic_delta_nic) in
  let val nic_delta_nic_regs_cppi_ram = mk_comb (``nic_regs_CPPI_RAM``, nic_delta_nic_regs) in
  let val args = [``q : bd_pa_type list``, ``nic.regs.CPPI_RAM``, nic_delta_nic_regs_cppi_ram] in
  let val suc = list_mk_comb (``EQ_BDs``, args) in
  let val imp = mk_imp (ant, suc) in
  let val goal = list_mk_forall (quantifiers @ [``q : bd_pa_type list``], imp) in
    (goal, tx_id)
  end end end end end end end end end end end end end end end;

fun solve_eq_bds_goal (tx_id : int) = 
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ONCE_REWRITE_TAC [NO_BD_LIST_OVERLAP_SYM_lemma] THEN
  EXISTS_TAC ((#1 o dest_eq o #2 o strip_forall o concl) (txLib.get_tx_conjunct NIC_DELTA_CPPI_RAM_WRITE_STEP_BD_PAs_CONJ_defs tx_id)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``tx_bd_queue nic`` TX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  (fn g =>
   let val lemma = txLib.get_tx_conjunct NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas tx_id in
     if (is_imp o #2 o strip_forall o concl) lemma then
       (MATCH_MP_TAC lemma THEN
        ASM_REWRITE_TAC []) g
     else
        ASM_REWRITE_TAC [lemma] g
   end);

(* Theorems of the form:
   |- ∀nic env q.
     TX_STATE_WRITE_CP nic ∧ TX_INVARIANT_WELL_DEFINED nic ∧
     BDs_IN_CPPI_RAM q ∧ NO_BD_LIST_OVERLAP q (tx_bd_queue nic) ⇒
     EQ_BDs q nic.regs.CPPI_RAM (tx_6write_cp env nic).regs.CPPI_RAM *)
val TX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemmas =
  let fun prove_lemma lemma =
    let val (goal, tx_id) = create_eq_bds_goal_tx_id lemma
    in
      prove (goal, solve_eq_bds_goal tx_id)
    end
  in
    boolTheory.TRUTH::map prove_lemma (tl (CONJ_LIST 7 NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_CONJ_lemmas))
  end;

val TX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_CONJ_lemmas =
  LIST_CONJ TX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemmas;



fun prove_eq_bds (tx_id : int) =
 ASSUME_TAC ((UNDISCH o SPEC_ALL) (txLib.get_tx_conjunct TX_STATE_TRANSITION_IMP_TX_TRANSITION_STEP_EQ_CONJ_lemmas tx_id)) THEN
 ASM_RW_ASM_TAC ``tx_transition env nic = x`` ``(nic', mr') = tx_transition env nic`` THEN
 ((RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
   PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm))) ORELSE
  (ASSUME_TAC (UNDISCH (SPEC_ALL tx_2issue_next_memory_read_request_lemmasTheory.tx_2issue_next_memory_read_request_FST_lemma)))) THEN
 ASM_REWRITE_TAC [] THEN
 (let val tx_transition_function = txLib.tx_id_to_tx_transition_function tx_id
  in
    if is_abs tx_transition_function then
      ONCE_REWRITE_TAC [(SYM o BETA_CONV o mk_comb) (tx_transition_function, ``nic : nic_state``)]
    else
      ALL_TAC
  end) THEN
 MATCH_MP_TAC (txLib.get_tx_conjunct TX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_CONJ_lemmas tx_id) THEN
 ASM_REWRITE_TAC [];

val tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_transition_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic env nic' mr' q.
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    TX_INVARIANT_WELL_DEFINED nic /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL tx_state_lemmasTheory.TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TX_STATE_CASEs_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val left_disjunct = (#1 o dest_disj o concl) thm in
    let val tx_id = txLib.tx_transition_state_application_to_tx_id left_disjunct in
      ASM_CASES_TAC left_disjunct THENL
      [
       prove_eq_bds tx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_eq_bds 6);

val tx_memory_read_reply_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma = store_thm (
  "tx_memory_read_reply_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_lemma",
  ``!nic mr nic' q.
    (nic' = tx_3process_memory_read_reply mr nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT_WELL_DEFINED nic /\
    BDs_IN_CPPI_RAM q /\
    NO_BD_LIST_OVERLAP q (tx_bd_queue nic)
    ==>
    EQ_BDs q nic.regs.CPPI_RAM nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (txLib.get_tx_conjunct TX_NIC_DELTA_PRESERVES_BD_QUEUE_NOT_OVERLAPPING_TX_BD_QUEUE_CONJ_lemmas 3))) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

