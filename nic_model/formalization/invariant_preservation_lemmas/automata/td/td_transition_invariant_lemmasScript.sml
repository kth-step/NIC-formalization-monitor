open HolKernel Parse boolLib bossLib;
open helperTactics;
open td_0idle_lemmasTheory;
open td_1set_eoq_lemmasTheory;
open td_2set_td_lemmasTheory;
open td_3clear_owner_and_hdp_lemmasTheory;
open td_4write_cp_lemmasTheory;
open tdTheory;
open td_state_definitionsTheory;
open td_transition_definitionsTheory;
open bd_queue_preservation_lemmasTheory;
open td_invariant_preservation_definitionsTheory;
open tx_transition_definitionsTheory;
open it_transition_definitionsTheory;
open rx_transition_definitionsTheory;
open rd_transition_definitionsTheory;
open tdInvariantTheory;
open it_state_lemmasTheory;
open rx_state_lemmasTheory;
open bd_listTheory;
open rx_bd_queueTheory;
open rxInvariantTheory;
open rxInvariantWellDefinedTheory;
open rxInvariantWellDefinedLemmasTheory;
open schedulerTheory;
open tx_state_definitionsTheory;

val _ = new_theory "td_transition_invariant_lemmas";

(**************************************************)
(* Start of proofs of the form:
   |- !nic env.
      TD_STATE_IDLE nic
      ==>
      (td_transition env nic = td_0idle nic)``

   and definitions of related lists and function. *)
(**************************************************)

val td_transition_function_defs = [
  td_0idle_def,
  td_1set_eoq_def,
  td_2set_td_def,
  td_3clear_owner_and_hdp_def,
  td_4write_cp_def];

fun td_id_to_td_transition_function_def (td_id : int) =
  List.nth (td_transition_function_defs, td_id);

val td_transition_function_applications =
  map (#1 o dest_eq o #2 o strip_forall o concl) td_transition_function_defs;

fun td_id_to_td_transition_function_application (td_id : int) =
  List.nth (td_transition_function_applications, td_id);

val td_state_defs = [
  TD_STATE_IDLE_def,
  TD_STATE_SET_EOQ_def,
  TD_STATE_SET_TD_def,
  TD_STATE_CLEAR_OWNER_AND_HDP_def,
  TD_STATE_WRITE_CP_def];

fun td_id_to_td_state_def (td_id : int) =
  List.nth (td_state_defs, td_id);

val td_state_applications = map (#1 o dest_eq o #2 o dest_forall o concl) td_state_defs;

fun td_id_to_td_state_application (td_id : int) =
  List.nth (td_state_applications, td_id);

(* Creates goals of the form:
   ``!nic env.
     TD_STATE_IDLE nic
     ==>
     (td_transition env nic = td_0idle nic)`` *)
fun create_td_state_imp_td_transition_eq_goal (td_id : int) =
  let val ant = td_id_to_td_state_application td_id in
  let val lhs = ``td_transition env nic`` in
  let val suc = mk_eq (lhs, td_id_to_td_transition_function_application td_id) in
  let val imp = mk_imp (ant, suc) in
  let val quantifiers = [``nic : nic_state``, ``env : environment``] in
  let val goal = list_mk_forall (quantifiers, imp) in
    goal
  end end end end end end;

(* Solves goals of the form:
   ``!nic env.
     TD_STATE_IDLE nic
     ==>
     (td_transition env nic = td_0idle nic)`` *)
fun solve_td_state_imp_td_transition_eq_goal (td_id : int) =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [td_id_to_td_state_def td_id] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [td_transition_def, stateTheory.td_abstract_state_case_def,
                   td_id_to_td_transition_function_def td_id];

(* Lemmas of the form:
   ``!nic env.
     TD_STATE_IDLE nic
     ==>
     (td_transition env nic = td_0idle nic)`` *)
val TD_STATE_IMP_td_transition_eq_lemmas =
  let fun prove_thm td_id =
    let val goal = create_td_state_imp_td_transition_eq_goal td_id in
    let val tactic = solve_td_state_imp_td_transition_eq_goal td_id in
    let val thm = prove (goal, tactic) in
      if td_id = 4 then
        [thm]
      else
        thm::prove_thm (td_id + 1)
    end end end
  in
    prove_thm 0
  end;

fun td_id_to_TD_STATE_IMP_td_transition_eq_lemma (td_id : int) =
  List.nth (TD_STATE_IMP_td_transition_eq_lemmas, td_id);

fun td_id_to_td_state_eq_IMP_td_transition_eq_lemma (td_id : int) =
  REWRITE_RULE td_state_defs (List.nth (TD_STATE_IMP_td_transition_eq_lemmas, td_id));

(**************************************************)
(* End of proofs of the form:
   |- !nic env.
      TD_STATE_IDLE nic
      ==>
      (td_transition env nic = td_0idle nic)``

   and definitions of related lists and function. *)
(**************************************************)


















(**********************************************************************************************)
(* Start of proofs of the form:
   |- !nic env.
      TD_STATE_IDLE nic
      ==>
      (td_transition_cppi_ram_write_step_bd_pas env nic = td_0idle_cppi_ram_write_step_bd_pas)

   and definitions of related lists and function. *)
(**********************************************************************************************)

val td_transition_cppi_ram_write_step_bd_pas_def = Define `
  td_transition_cppi_ram_write_step_bd_pas env nic =
  case nic.td.state of
    | td_idle => td_0idle_cppi_ram_write_step_bd_pas
    | td_set_eoq => td_1set_eoq_cppi_ram_write_step_bd_pas env nic
    | td_set_td => td_2set_td_cppi_ram_write_step_bd_pas nic
    | td_clear_owner_and_hdp => td_3clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic
    | td_write_cp => td_4write_cp_cppi_ram_write_step_bd_pas`;

val td_transition_function_cppi_ram_write_step_bd_pas_defs = [
  td_0idle_cppi_ram_write_step_bd_pas_def,
  td_1set_eoq_cppi_ram_write_step_bd_pas_def,
  td_2set_td_cppi_ram_write_step_bd_pas_def,
  td_3clear_owner_and_hdp_cppi_ram_write_step_bd_pas_def,
  td_4write_cp_cppi_ram_write_step_bd_pas_def];

val td_transition_function_cppi_ram_write_step_bd_pas_applications =
  map
  (#1 o dest_eq o #2 o strip_forall o concl)
  td_transition_function_cppi_ram_write_step_bd_pas_defs;

fun td_id_to_td_transition_function_cppi_ram_write_step_bd_pas_application_def (td_id : int) =
  List.nth (td_transition_function_cppi_ram_write_step_bd_pas_applications, td_id);

(* Creates goals of the form:
   ``!nic env.
     TD_STATE_IDLE nic
     ==>
     (td_transition_cppi_ram_write_step_bd_pas env nic = td_0idle_cppi_ram_write_step_bd_pas)`` *)
fun create_td_state_imp_td_transition_cppi_ram_write_step_bd_pas_eq_goal (td_id : int) =
  let val ant = td_id_to_td_state_application td_id in
  let val lhs = ``td_transition_cppi_ram_write_step_bd_pas env nic`` in
  let val rhs = td_id_to_td_transition_function_cppi_ram_write_step_bd_pas_application_def td_id in
  let val suc = mk_eq (lhs, rhs) in
  let val imp = mk_imp (ant, suc) in
  let val quantifiers = [``nic : nic_state``, ``env : environment``] in
  let val goal = list_mk_forall (quantifiers, imp) in
    goal
  end end end end end end end;

(* Solves a goal of the form:
   ``!nic env.
     TD_STATE_IDLE nic
     ==>
     (td_transition_cppi_ram_write_step_bd_pas env nic = td_0idle_cppi_ram_write_step_bd_pas)`` *)
val solve_td_state_imp_td_transition_cppi_ram_write_step_bd_pas_eq_goal =
  REPEAT GEN_TAC THEN
  REWRITE_TAC td_state_defs THEN
  DISCH_TAC THEN
  REWRITE_TAC [td_transition_cppi_ram_write_step_bd_pas_def] THEN
  ASM_REWRITE_TAC [stateTheory.td_abstract_state_case_def];

(* Lemmas of the form:
   |- !nic env.
      TD_STATE_IDLE nic
      ==>
      (td_transition_cppi_ram_write_step_bd_pas env nic = td_0idle_cppi_ram_write_step_bd_pas) *)
val TD_STATE_IMP_td_transition_cppi_ram_write_step_bd_pas_eq_lemmas =
  let fun prove_thm td_id =
    let val goal = create_td_state_imp_td_transition_cppi_ram_write_step_bd_pas_eq_goal td_id in
    let val tactic = solve_td_state_imp_td_transition_cppi_ram_write_step_bd_pas_eq_goal in
    let val thm = prove (goal, tactic) in
      if td_id = 4 then
        [thm]
      else
        thm::prove_thm (td_id + 1)
    end end end
  in
    prove_thm 0
  end;

fun td_id_to_td_state_imp_td_transition_cppi_ram_write_step_bd_pas_eq_lemma (td_id : int) =
  List.nth (TD_STATE_IMP_td_transition_cppi_ram_write_step_bd_pas_eq_lemmas, td_id);

fun td_id_to_td_state_eq_imp_td_transition_cppi_ram_write_step_bd_pas_eq_lemma (td_id : int) =
  REWRITE_RULE
  td_state_defs
  (List.nth (TD_STATE_IMP_td_transition_cppi_ram_write_step_bd_pas_eq_lemmas, td_id));

(**********************************************************************************************)
(* End of proofs of the form:
   |- !nic env.
      TD_STATE_IDLE nic
      ==>
      (td_transition_cppi_ram_write_step_bd_pas env nic = td_0idle_cppi_ram_write_step_bd_pas)

   and definitions of related lists and function. *)
(**********************************************************************************************)




(******************************************************************************)
(* Given a term of the form ``nic.td.state = td_<state_name>, returns its id. *)
(******************************************************************************)
fun td_abstract_state_eq_to_td_id (eq_tm : term) =
  let val td_abstract_state = (#2 o dest_eq) eq_tm in
  let val td_abstract_state2num_tm = mk_comb (``td_abstract_state2num``, td_abstract_state) in
  let val td_abstract_states2num_eq_tms =
    (strip_conj o concl) stateTheory.td_abstract_state2num_thm in
  let val td_abstract_states_index_pairs =
   map (fn tm => ((#1 o dest_eq) tm, (#2 o dest_eq) tm)) td_abstract_states2num_eq_tms in
  let fun comp (state, index) = state = td_abstract_state2num_tm in
  let val td_abstract_state_index_pair = List.find comp td_abstract_states_index_pairs in
  let val index = (#2 o getOpt) (td_abstract_state_index_pair, (``F``, ``F``)) in
  let val td_id = (string_to_int o term_to_string) index in
    td_id
  end end end end end end end end;

(*********************************************************************)
(* Given a term of the form ``TD_STATE_<STATE_NAME>, returns its id. *)
(*********************************************************************)
fun td_state_to_td_id (td_state : term) = 
  let val td_abstract_state = (concl o (REWRITE_RULE td_state_defs)) (ASSUME td_state) in
    td_abstract_state_eq_to_td_id td_abstract_state
  end;







val TD_AUTONOMOUS_TRANSITION_IMP_TD_TRANSITION_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_TD_TRANSITION_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic' = td_transition env nic)``,
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val TD_AUTONOMOUS_TRANSITION_IMP_TX_STATE_IDLE_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_TX_STATE_IDLE_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    TX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [schedulerTheory.TD_ENABLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [tx_state_definitionsTheory.TX_STATE_IDLE_def]);







(***************************************************************)
(***************************************************************)
(* Start of NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE *)
(***************************************************************)
(***************************************************************)


(*******************************************************************)
(* Start of NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs *)
(*******************************************************************)

val TD_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemmas = [
  td_0idle_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma,
  td_1set_eoq_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma,
  td_2set_td_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma,
  td_3clear_owner_and_hdp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma,
  td_4write_cp_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma];

val td_transition_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma = store_thm (
  "td_transition_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma",
  ``!nic env.
    NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
    (td_transition env)
    nic
    (td_transition_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  Cases_on `nic.td.state` THEN
    PAT_ASSUM ``P`` (fn thm =>
      let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
      let val lemma1 =
        td_id_to_td_state_eq_imp_td_transition_cppi_ram_write_step_bd_pas_eq_lemma td_id in
      let val lemma2 =
        td_id_to_td_state_eq_IMP_td_transition_eq_lemma td_id in
      let val rw_lemmas =
        map
        (REWRITE_RULE [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def])
        TD_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemmas
      in
        ASSUME_TAC (UNDISCH (SPEC_ALL lemma1)) THEN
        ASSUME_TAC (UNDISCH (SPEC_ALL lemma2)) THEN
        ASM_REWRITE_TAC rw_lemmas
      end end end end));

(*****************************************************************)
(* End of NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs *)
(*****************************************************************)

(*******************************************************)
(* Start of CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE *)
(*******************************************************)

val TD_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemmas = [
  td_0idle_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma,
  td_1set_eoq_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma,
  td_2set_td_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma,
  td_3clear_owner_and_hdp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma,
  td_4write_cp_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma];

fun td_id_to_td_delta_cppi_ram_write_steps_write_bd_at_current_bd_pa_lemma (td_id : int) =
  List.nth (TD_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemmas, td_id);

val td_transition_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "td_transition_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
    (td_transition_cppi_ram_write_step_bd_pas env nic)
    [nic.tx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  Cases_on `nic.td.state` THEN
  PAT_ASSUM ``P`` (fn thm =>
    let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
    let val lemma1 =
      td_id_to_td_state_eq_imp_td_transition_cppi_ram_write_step_bd_pas_eq_lemma td_id in
    let val lemma2 =
      td_id_to_td_delta_cppi_ram_write_steps_write_bd_at_current_bd_pa_lemma td_id in
      ASSUME_TAC (UNDISCH (SPEC_ALL lemma1)) THEN
      ASM_REWRITE_TAC [lemma2]
    end end end));

(*****************************************************)
(* End of CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE *)
(*****************************************************)

(********************************************************)
(* Start of PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION *)
(********************************************************)

val TD_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemmas = [
  td_0idle_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma,
  td_1set_eoq_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma,
  td_2set_td_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma,
  td_3clear_owner_and_hdp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma,
  td_4write_cp_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma];

fun td_id_to_td_delta_preserves_non_overlapping_bd_queue_location_lemma (td_id : int) =
  List.nth (TD_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemmas, td_id);

val td_transition_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma = store_thm (
  "td_transition_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma",
  ``!nic env.
    PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
    (td_transition_cppi_ram_write_step_bd_pas env nic)``,
  REPEAT GEN_TAC THEN
  Cases_on `nic.td.state` THEN
  PAT_ASSUM ``P`` (fn thm =>
    let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
    let val lemma =
      td_id_to_td_state_eq_imp_td_transition_cppi_ram_write_step_bd_pas_eq_lemma td_id in
      ASSUME_TAC (UNDISCH (SPEC_ALL lemma)) THEN
      ASM_REWRITE_TAC TD_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemmas
    end end));

(******************************************************)
(* End of PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION *)
(******************************************************)

val td_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "td_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (td_transition env)
    nic
    (td_transition_cppi_ram_write_step_bd_pas env nic)
    [nic.tx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [td_transition_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_lemma] THEN
  REWRITE_TAC [td_transition_CPPI_RAM_WRITE_STEPs_WRITE_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [td_transition_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_lemma]);

(*************************************************************)
(*************************************************************)
(* End of NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE *)
(*************************************************************)
(*************************************************************)



(****************************************************************)
(* Start of NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM *)
(****************************************************************)

val TD_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemmas = [
  td_0idle_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma,
  td_1set_eoq_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma,
  td_2set_td_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma,
  td_3clear_owner_and_hdp_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma,
  td_4write_cp_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma];

fun td_id_to_reverse_preserved_td_state_write_cppi_ram_lemma (td_id : int) =
  List.nth (TD_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemmas, td_id);

fun td_id_to_imp_reverse_preserved_td_state_write_cppi_ram_lemma (td_id : int) =
  REWRITE_RULE
  [NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def]
  (td_id_to_reverse_preserved_td_state_write_cppi_ram_lemma td_id);

val td_transition_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "td_transition_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma",
  ``!env. NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM (td_transition env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def] THEN
  GEN_TAC THEN
  Cases_on `nic.td.state` THEN
  PAT_ASSUM ``P`` (fn thm =>
    let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
    let val td_transition_eq_lemma = td_id_to_td_state_eq_IMP_td_transition_eq_lemma td_id in
    let val td_case_lemma = td_id_to_imp_reverse_preserved_td_state_write_cppi_ram_lemma td_id in
      ASSUME_TAC (UNDISCH (SPEC_ALL td_transition_eq_lemma)) THEN
      ASM_REWRITE_TAC [td_case_lemma]
    end end end));

(**************************************************************)
(* End of NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM *)
(**************************************************************)




(*************************************************************************************)
(* Start of NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA *)
(*************************************************************************************)

val TD_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemmas = [
  td_0idle_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma,
  td_1set_eoq_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma,
  td_2set_td_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma,
  td_3clear_owner_and_hdp_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma,
  td_4write_cp_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma];

fun td_id_to_td_write_current_bd_pa_neq_zero_imp_preserves_tx_current_bd_pa_lemma (td_id : int) =
  List.nth (TD_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemmas, td_id);

fun td_id_to_imp_td_write_current_bd_pa_neq_zero_imp_preserves_tx_current_bd_pa_lemma (td_id : int) =
  REWRITE_RULE
  [NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_def,
   NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA_def]
  (List.nth (TD_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemmas, td_id));

val td_transition_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma = store_thm (
  "td_transition_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma",
  ``!env.
    NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA (td_transition env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  Cases_on `nic.td.state` THEN
  PAT_ASSUM ``(nic : nic_state).td.state = x`` (fn thm =>
    let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
    let val td_transition_eq_lemma = td_id_to_td_state_eq_IMP_td_transition_eq_lemma td_id in
    let val td_case_lemma =
      td_id_to_imp_td_write_current_bd_pa_neq_zero_imp_preserves_tx_current_bd_pa_lemma td_id in
    let val nic_prime_eq_td_transition = ``nic' = td_transition env nic`` in
    let val td_transition_eq_td_case_transition =
      (#2 o dest_imp o #2 o strip_forall o concl) td_transition_eq_lemma
    in
      ASSUME_TAC (UNDISCH (SPEC_ALL td_transition_eq_lemma)) THEN
      KEEP_ASM_RW_ASM_TAC td_transition_eq_td_case_transition nic_prime_eq_td_transition THEN
      ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL td_case_lemma)) THEN
      ASM_REWRITE_TAC []
    end end end end end));

(********************************************************************************)
(* End NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA *)
(********************************************************************************)




(*****************************************************)
(* Start of NIC_DELTA_PRESERVES_TX_STATE_IT_RX_lemma *)
(*****************************************************)

val TD_DELTA_PRESERVES_TX_STATE_IT_RX_RD_lemmas = [
  td_0idle_PRESERVES_TX_STATE_IT_RX_RD_lemma,
  td_1set_eoq_PRESERVES_TX_STATE_IT_RX_RD_lemma,
  td_2set_td_PRESERVES_TX_STATE_IT_RX_RD_lemma,
  td_3clear_owner_and_hdp_PRESERVES_TX_STATE_IT_RX_RD_lemma,
  td_4write_cp_PRESERVES_TX_STATE_IT_RX_RD_lemma];

fun td_id_to_unfolded_preserves_tx_state_it_rx_lemma (td_id : int) =
  REWRITE_RULE
  [NIC_DELTA_PRESERVES_TX_STATE_def, NIC_DELTA_PRESERVES_IT_def, NIC_DELTA_PRESERVES_RX_def, NIC_DELTA_PRESERVES_RD_def]
  (List.nth (TD_DELTA_PRESERVES_TX_STATE_IT_RX_RD_lemmas, td_id));

val td_transition_PRESERVES_TX_STATE_IT_RX_RD_lemma = store_thm (
  "td_transition_PRESERVES_TX_STATE_IT_RX_RD_lemma",
  ``!env.
    NIC_DELTA_PRESERVES_TX_STATE (td_transition env) /\
    NIC_DELTA_PRESERVES_IT (td_transition env) /\
    NIC_DELTA_PRESERVES_RX (td_transition env) /\
    NIC_DELTA_PRESERVES_RD (td_transition env)``,
  GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_STATE_def, NIC_DELTA_PRESERVES_IT_def, NIC_DELTA_PRESERVES_RX_def, NIC_DELTA_PRESERVES_RD_def] THEN
  let val tactic =
    Cases_on `nic.td.state` THEN
    PAT_ASSUM ``(nic : nic_state).td.state = x`` (fn thm =>
      let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
      let val td_transition_eq_lemma = td_id_to_td_state_eq_IMP_td_transition_eq_lemma td_id in
      let val td_case_lemma = td_id_to_unfolded_preserves_tx_state_it_rx_lemma td_id in
        ASSUME_TAC (UNDISCH (SPEC_ALL td_transition_eq_lemma)) THEN
        ASM_REWRITE_TAC [td_case_lemma]
      end end end)
  in
    CONJ_TAC THENL
    [
     GEN_TAC THEN
     tactic
     ,
     CONJ_TAC THENL
     [
      GEN_TAC THEN
      tactic
      ,
      CONJ_TAC THEN
      GEN_TAC THEN
      tactic
     ]
    ]
  end);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.tx.state = nic.tx.state) /\
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC [REWRITE_RULE [NIC_DELTA_PRESERVES_TX_STATE_def, NIC_DELTA_PRESERVES_IT_def, NIC_DELTA_PRESERVES_RX_def, NIC_DELTA_PRESERVES_RD_def] td_transition_PRESERVES_TX_STATE_IT_RX_RD_lemma]);

(********************************************************************************)
(* End NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA *)
(********************************************************************************)

val NIC_DELTA_MP_PRESERVES_TX_CURRENT_BD_PA_lemma = store_thm (
  "NIC_DELTA_MP_PRESERVES_TX_CURRENT_BD_PA_lemma",
  ``!nic nic_delta nic'.
    (nic' = nic_delta nic) /\
    TD_STATE_WRITE_CPPI_RAM nic' /\
    NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA nic_delta
    ==>
    (nic'.tx.current_bd_pa = nic.tx.current_bd_pa)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_TX_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  EXISTS_TAC ``nic' : nic_state`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVES_IT_RX_RD_IMP_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_IT_RX_RD_IMP_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic nic_delta nic'.
    (nic' = nic_delta nic) /\
    NIC_DELTA_PRESERVES_IT nic_delta /\
    NIC_DELTA_PRESERVES_RX nic_delta /\
    NIC_DELTA_PRESERVES_RD nic_delta /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'
    ==>
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_IT_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_def] THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RD_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT (PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``nic : nic_state`` thm))) THEN
  REFLECT_ASM_TAC ``nic' : nic_state = nic_delta nic`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic_delta nic = nic'`` ``(nic_delta nic).it = x`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic_delta nic = nic'`` ``(nic_delta : nic_delta_type nic).rx = x`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic_delta nic = nic'`` ``(nic_delta : nic_delta_type nic).rd = x`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL EQ_INIT_IMP_EQ_INIT_STATE_lemma)) THEN
  MATCH_MP_TAC RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma THEN
  EXISTS_TAC ``nic' : nic_state`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_MP_TD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "NIC_DELTA_MP_TD_STATE_WRITE_CPPI_RAM_lemma",
  ``!nic nic_delta nic'.
    (nic' = nic_delta nic) /\
    NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM nic_delta /\
    TD_STATE_WRITE_CPPI_RAM nic'
    ==>
    TD_STATE_WRITE_CPPI_RAM nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_RW_ASM_TAC ``x = y`` ``P`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVING_TX_STATE_IT_RX_RD_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "NIC_DELTA_PRESERVING_TX_STATE_IT_RX_RD_PRESERVES_TD_INVARIANT_lemma",
  ``!nic nic_delta nic' cppi_ram_write_step_bd_pas.
    (nic' = nic_delta nic) /\
    TD_INVARIANT nic /\
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas [nic.tx.current_bd_pa] /\
    NIC_DELTA_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM nic_delta /\
    NIC_DELTA_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA nic_delta /\
    NIC_DELTA_PRESERVES_TX_STATE nic_delta /\
    NIC_DELTA_PRESERVES_IT nic_delta /\
    NIC_DELTA_PRESERVES_RX nic_delta /\
    NIC_DELTA_PRESERVES_RD nic_delta
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_INVARIANT_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_PRESERVES_IT_RX_RD_IMP_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_MP_TD_STATE_WRITE_CPPI_RAM_lemma)) THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_MP_PRESERVES_TX_CURRENT_BD_PA_lemma)) THEN
  PAT_ASSUM ``nic'.tx.current_bd_pa = nic.tx.current_bd_pa`` (fn thm => REWRITE_TAC [thm]) THEN
  PAT_ASSUM ``BD_IN_CPPI_RAM nic.tx.current_bd_pa`` (fn thm => ASSUME_TAC thm THEN REWRITE_TAC [thm]) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic.tx.current_bd_pa`` BD_IN_CPPI_RAM_IMP_BD_SINGLETON_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``BD_NOT_OVERLAP_BDs nic.tx.current_bd_pa (rx_bd_queue nic)`` BD_NOT_OVERLAP_BDs_EQ_NO_BD_LIST_OVERLAP_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (SPECL [``[nic.tx.current_bd_pa]``, ``rx_bd_queue nic``, ``nic_delta : nic_delta_type``, ``nic : nic_state``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma))) THEN
  REWRITE_TAC [rx_bd_queue_def] THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_EQ_NO_BD_LIST_OVERLAP_lemma] THEN
  MATCH_MP_TAC EQ_BDs_IMP_NO_BD_LIST_OVERLAP_PRESERVED_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``(nic_delta (nic : nic_state)).regs.CPPI_RAM``] BD_QUEUE_EQ_BDs_IMP_EQ_BD_QUEUEs_lemma)) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX nic_delta`` NIC_DELTA_PRESERVES_RX_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  ASM_REWRITE_TAC [GSYM rx_bd_queue_def]);

val td_transition_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "td_transition_PRESERVES_TD_INVARIANT_lemma",
  ``!nic env nic'.
    (nic' = td_transition env nic) /\
    TD_INVARIANT nic /\
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic)
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_PRESERVING_TX_STATE_IT_RX_RD_PRESERVES_TD_INVARIANT_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``td_transition env`` THEN
  EXISTS_TAC ``td_transition_cppi_ram_write_step_bd_pas env nic`` THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [td_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [td_transition_REVERSE_PRESERVED_TD_STATE_WRITE_CPPI_RAM_lemma] THEN
  REWRITE_TAC [td_transition_TD_WRITE_CURRENT_BD_PA_NEQ_ZERO_IMP_PRESERVES_TX_CURRENT_BD_PA_lemma] THEN
  REWRITE_TAC [td_transition_PRESERVES_TX_STATE_IT_RX_RD_lemma]);

val TD_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'
    ==>
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TD_TRANSITION_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (REWRITE_RULE [td_transition_PRESERVES_TX_STATE_IT_RX_RD_lemma] (SPECL [``nic : nic_state``, ``td_transition env``, ``nic' : nic_state``] NIC_DELTA_PRESERVES_IT_RX_RD_IMP_REVERSE_PRESERVES_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)))) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_RX_BD_QUEUE_IN_CPPI_RAM_PRESERVES_TD_INVARIANT_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_RX_BD_QUEUE_IN_CPPI_RAM_PRESERVES_TD_INVARIANT_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    TD_INVARIANT nic /\
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic)
    ==>
    TD_INVARIANT nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC td_transition_PRESERVES_TD_INVARIANT_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_RX_INVARIANT_IMP_RX_BD_QUEUE_IN_CPPI_RAM_lemma = store_thm (
  "RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_RX_INVARIANT_IMP_RX_BD_QUEUE_IN_CPPI_RAM_lemma",
  ``!nic WRITABLE.
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    RX_INVARIANT nic WRITABLE
    ==>
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_def] THEN
  REWRITE_TAC [RX_INVARIANT_MEMORY_def] THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma]);

val TD_DELTA_PRESERVES_DEAD_lemmas = [
  boolTheory.TRUTH,
  td_1set_eoq_PRESERVES_DEAD_lemma,
  td_2set_td_PRESERVES_DEAD_lemma,
  td_3clear_owner_and_hdp_PRESERVES_DEAD_lemma,
  td_4write_cp_PRESERVES_DEAD_lemma];

fun td_id_to_td_delta_preserves_dead_lemma (td_id : int) =
  List.nth (TD_DELTA_PRESERVES_DEAD_lemmas, td_id);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL td_state_lemmasTheory.TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TD_STATE_CASEs_lemma)) THEN
  (let fun tactic td_id =
     ASSUME_TAC (UNDISCH (SPEC_ALL (td_id_to_TD_STATE_IMP_td_transition_eq_lemma td_id))) THEN
     ASM_RW_ASM_TAC ``td_transition env nic = x`` ``nic' = td_transition env nic`` THEN
     ASSUME_TAC (UNDISCH (SPEC_ALL (td_id_to_td_delta_preserves_dead_lemma td_id))) THEN
     ASM_REWRITE_TAC []
   in
     REPEAT (PAT_ASSUM ``P \/ Q`` (fn disjunction =>
       let val left_disjunct = (#1 o dest_disj o concl) disjunction in
       let val td_id = td_state_to_td_id left_disjunct in
         ASM_CASES_TAC left_disjunct THENL
         [
          tactic td_id
          ,
          ASSUME_TAC disjunction THEN
          ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
         ]
       end end)) THEN
     tactic 4
   end));






val TD_DELTA_PRESERVES_RX_BUFFER_OFFSET_lemmas = [
  boolTheory.TRUTH,
  td_1set_eoq_PRESERVES_RX_BUFFER_OFFSET_lemma,
  td_2set_td_PRESERVES_RX_BUFFER_OFFSET_lemma,
  td_3clear_owner_and_hdp_PRESERVES_RX_BUFFER_OFFSET_lemma,
  td_4write_cp_PRESERVES_RX_BUFFER_OFFSET_lemma];

fun td_id_to_td_delta_preserves_rx_buffer_offset_lemma (td_id : int) =
  List.nth (TD_DELTA_PRESERVES_RX_BUFFER_OFFSET_lemmas, td_id);

val TD_AUTONOMOUS_TRANSITION_PRESERVES_RX_BUFFER_OFFSET_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_PRESERVES_RX_BUFFER_OFFSET_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL td_state_lemmasTheory.TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_TD_STATE_CASEs_lemma)) THEN
  (let fun tactic td_id =
     ASSUME_TAC (UNDISCH (SPEC_ALL (td_id_to_TD_STATE_IMP_td_transition_eq_lemma td_id))) THEN
     ASM_RW_ASM_TAC ``td_transition env nic = x`` ``nic' = td_transition env nic`` THEN
     ASSUME_TAC (UNDISCH (SPEC_ALL (td_id_to_td_delta_preserves_rx_buffer_offset_lemma td_id))) THEN
     ASM_REWRITE_TAC []
   in
     REPEAT (PAT_ASSUM ``P \/ Q`` (fn disjunction =>
       let val left_disjunct = (#1 o dest_disj o concl) disjunction in
       let val td_id = td_state_to_td_id left_disjunct in
         ASM_CASES_TAC left_disjunct THENL
         [
          tactic td_id
          ,
          ASSUME_TAC disjunction THEN
          ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
         ]
       end end)) THEN
     tactic 4
   end));




val TD_DELTA_PRESERVES_CPPI_RAM_lemmas = [
  td_0idle_PRESERVES_CPPI_RAM_lemma,
  td_1set_eoq_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma,
  td_2set_td_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma,
  td_3clear_owner_and_hdp_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma,
  td_4write_cp_PRESERVES_CPPI_RAM_lemma];

fun td_id_to_td_delta_preserves_cppi_ram_lemma (td_id : int) =
  List.nth (TD_DELTA_PRESERVES_CPPI_RAM_lemmas, td_id);

val td_transition_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma = store_thm (
  "td_transition_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma",
  ``!nic env nic'.
    (nic' = td_transition env nic) /\
    ~TD_WRITE_CURRENT_BD_PA nic
    ==>
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.td.state` THEN
  PAT_ASSUM ``nic.td.state = x`` (fn thm =>
    let val td_id = (td_abstract_state_eq_to_td_id o concl) thm in
      ASSUME_TAC (UNDISCH (SPEC_ALL (td_id_to_td_state_eq_IMP_td_transition_eq_lemma td_id))) THEN
      ASM_RW_ASM_TAC ``td_transition env nic = x`` ``nic' = td_transition env nic`` THEN
      ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (td_id_to_td_delta_preserves_cppi_ram_lemma td_id)))
    end) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    ~TD_WRITE_CURRENT_BD_PA nic
    ==>
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL td_transition_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_PRESERVATION_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_PRESERVATION_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic' /\
    ~TD_WRITE_CURRENT_BD_PA nic
    ==>
    (nic'.dead = nic.dead) /\
    (nic'.it = nic.it) /\
    (nic'.rx = nic.rx) /\
    (nic'.rd = nic.rd) /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_DEAD_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_RX_BUFFER_OFFSET_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TD_AUTONOMOUS_TRANSITION_NOT_TD_WRITE_CURRENT_BD_PA_IMP_PRESERVES_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val TD_AUTONOMOUS_TRANSITION_IMP_NEXT_TX_STATE_IDLE_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_NEXT_TX_STATE_IDLE_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    TX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TX_STATE_IDLE_lemma)) THEN
  RW_ASM_TAC ``TX_STATE_IDLE nic`` TX_STATE_IDLE_def THEN
  ASM_REWRITE_TAC [TX_STATE_IDLE_def]);

val TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    ~TX_STATE_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_PRESERVES_TX_STATE_IT_RX_RD_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_TX_STATE_IDLE_lemma)) THEN
  RW_ASM_TAC ``TX_STATE_IDLE nic`` TX_STATE_IDLE_def THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``nic.tx.state = tx_idle`` ``nic'.tx.state = nic.tx.state`` THEN
  REWRITE_TAC [TX_STATE_PROCESS_MEMORY_READ_REPLY_def] THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [stateTheory.tx_abstract_state_distinct]);

val TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    TD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    ~TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [TX_ENABLE_def] THEN
  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  REWRITE_TAC [GSYM TX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_NEXT_TX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TD_AUTONOMOUS_TRANSITION_IMP_NOT_NEXT_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

