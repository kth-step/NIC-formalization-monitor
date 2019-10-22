open HolKernel Parse boolLib bossLib;
open helperTactics;
open nic_rw_tactics;
open rdTheory;
open rd_transition_definitionsTheory;
open rdInvariantTheory;
open rd_0idle_lemmasTheory;
open rd_1set_sop_lemmasTheory;
open rd_2set_eop_lemmasTheory;
open rd_3set_eoq_lemmasTheory;
open rd_4set_td_lemmasTheory;
open rd_5clear_owner_and_hdp_lemmasTheory;
open rd_6write_cp_lemmasTheory;
open bd_queue_preservation_lemmasTheory;
open tx_state_definitionsTheory;
open tx_state_lemmasTheory;
open tx_transition_definitionsTheory;
open tx_bd_queueTheory;
open bd_listTheory;
open tx_invariant_lemmasTheory;
open rx_state_definitionsTheory;
open rd_state_definitionsTheory;
open rd_state_lemmasTheory;
open rd_transition_lemmasTheory;
open rx_transition_definitionsTheory;
open schedulerTheory;

val _ = new_theory "rd_transition_invariant_lemmas";

(*
[(``rd_0idle``, [``nic``]),
 (``rd_1set_sop``, [``env``, ``nic``]),
 (``rd_2set_eop``, [``env``, ``nic``]),
 (``rd_3set_eoq``, [``env``, ``nic``]),
 (``rd_4set_td``,  [``nic``]),
 (``rd_5clear_owner_and_hdp``, [``nic``]),
 (``rd_6write_cp``, [``env``, ``nic``])]
*)
val rd_delta_def_args =
  map
  (strip_comb o #2 o dest_eq o #2 o strip_forall)
  (strip_conj (concl rd_transition_case_def));

val rd_delta_defs = [
  rd_0idle_def,
  rd_1set_sop_def,
  rd_2set_eop_def,
  rd_3set_eoq_def,
  rd_4set_td_def,
  rd_5clear_owner_and_hdp_def,
  rd_6write_cp_def];

val nic_with_rw_tactic =
  rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors];

val rx_with_rw_tactic =
  rw_state_tactic
  `r`
  [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors];

val regs_with_rw_tactic =
  rw_state_tactic
  `n`
  [stateTheory.nic_regs_fn_updates, combinTheory.K_THM, stateTheory.nic_regs_accessors];


val RD_AUTONOMOUS_TRANSITION_WRITE_CURRENT_BD_PA_IMP_RD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_WRITE_CURRENT_BD_PA_IMP_RD_STATE_WRITE_CPPI_RAM_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_WRITE_CURRENT_BD_PA nic
    ==>
    RD_STATE_WRITE_CPPI_RAM nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma)) THEN
  ASM_REWRITE_TAC [RD_STATE_WRITE_CPPI_RAM_def]);

(**************************************************************************)
(* Start of lemmas for NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE *)
(**************************************************************************)

val rd_transition_cppi_ram_write_step_bd_pas_case_def = Define `
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_idle env nic =
   rd_0idle_cppi_ram_write_step_bd_pas) /\
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_set_sop env nic =
   rd_1set_sop_cppi_ram_write_step_bd_pas env nic) /\
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_set_eop env nic =
   rd_2set_eop_cppi_ram_write_step_bd_pas env nic) /\
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_set_eoq env nic =
   rd_3set_eoq_cppi_ram_write_step_bd_pas env nic) /\
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_set_td env nic =
   rd_4set_td_cppi_ram_write_step_bd_pas nic) /\
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_clear_owner_and_hdp env nic =
   rd_5clear_owner_and_hdp_cppi_ram_write_step_bd_pas nic) /\
  (rd_transition_cppi_ram_write_step_bd_pas_case rd_write_cp env nic =
   rd_6write_cp_cppi_ram_write_step_bd_pas)`;

val rd_transition_cppi_ram_write_step_bd_pas_def = Define `
  rd_transition_cppi_ram_write_step_bd_pas env nic =
  rd_transition_cppi_ram_write_step_bd_pas_case nic.rd.state env nic`;

val rd_delta_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemmas =
  map
  (REWRITE_RULE
     [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def,
      NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def,
      CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def,
      PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def])
  [rd_0idle_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma,
   rd_1set_sop_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma,
   rd_2set_eop_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma,
   rd_3set_eoq_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma,
   rd_4set_td_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma,
   rd_5clear_owner_and_hdp_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma,
   rd_6write_cp_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma];

val rd_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma = store_thm (
  "rd_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma",
  ``!nic env.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE
    (rd_transition env)
    nic
    (rd_transition_cppi_ram_write_step_bd_pas env nic)
    [nic.rx.current_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [rd_transition_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [rd_transition_cppi_ram_write_step_bd_pas_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC [rd_transition_cppi_ram_write_step_bd_pas_case_def] THEN
  REWRITE_TAC rd_delta_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_lemmas);

(**************************************************************************)
(* End of lemmas for NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE ***)
(**************************************************************************)




(******************************************************************************)
(*Start of lemmas regarding preservation of nic.rx.current_bd_pa***************)
(******************************************************************************)

val RX_CURRENT_BD_PA_EQ_def = Define `
  RX_CURRENT_BD_PA_EQ nic nic' = (nic'.rx.current_bd_pa = nic.rx.current_bd_pa)`;

val RX_CURRENT_BD_PA_EQ_ZERO_def = Define `
  RX_CURRENT_BD_PA_EQ_ZERO nic = (nic.rx.current_bd_pa = 0w)`;

val RX_CURRENT_BD_PA_EQ_OR_ZERO_def = Define `
  RX_CURRENT_BD_PA_EQ_OR_ZERO nic nic' =
  RX_CURRENT_BD_PA_EQ nic nic' \/
  RX_CURRENT_BD_PA_EQ_ZERO nic'`;

val RX_CURRENT_BD_PA_EQ_OR_ZERO_REVERSE_PRESERVES_RD_WRITE_CURRENT_BD_PA_lemma = store_thm (
  "RX_CURRENT_BD_PA_EQ_OR_ZERO_REVERSE_PRESERVES_RD_WRITE_CURRENT_BD_PA_lemma",
  ``!nic nic'.
    RD_WRITE_CURRENT_BD_PA nic' /\
    RX_CURRENT_BD_PA_EQ_OR_ZERO nic nic'
    ==>
    RD_WRITE_CURRENT_BD_PA nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_CASES_TAC ``RX_CURRENT_BD_PA_EQ nic nic'`` THENL
  [
   RW_ASM_TAC ``RX_CURRENT_BD_PA_EQ nic nic'`` RX_CURRENT_BD_PA_EQ_def THEN
   ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   RW_ASM_TAC ``RX_CURRENT_BD_PA_EQ_ZERO nic'`` RX_CURRENT_BD_PA_EQ_ZERO_def THEN
   ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val rd_0idle_preserves_rx_current_bd_pa_tactic =
  GEN_TAC THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic;

val rd_1_2_3_4delta_preserves_rx_current_bd_pa_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  REPEAT (COND_CASES_TAC THENL
  [
   nic_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  RW_ASM_TAC ``~P (nic : nic_state)`` RD_WRITE_CURRENT_BD_PA_def THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_5clear_owner_and_hdp_clears_rx_current_bd_pa_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_ZERO_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_6write_cp_clears_rx_current_bd_pa_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_delta_preserves_or_clears_rx_current_bd_pa_tacitcs =
  let fun set_fun (i : int) =
    if i = 0 then
      rd_0idle_preserves_rx_current_bd_pa_tactic::set_fun (i + 1)
    else if 1 <= i andalso i <= 4 then
      rd_1_2_3_4delta_preserves_rx_current_bd_pa_tactic::set_fun (i + 1)
    else if i = 5 then
      rd_5clear_owner_and_hdp_clears_rx_current_bd_pa_tactic::set_fun (i + 1)
    else if i = 6 then
      [rd_6write_cp_clears_rx_current_bd_pa_tactic]
    else
      raise Fail "rd_delta_preserves_or_clears_rx_current_bd_pa_tacitcs: Index out of bounds."
  in
    set_fun 0
  end;

fun create_rd_delta_preserves_or_clears_rx_current_bd_pa_goal (rd_delta, rd_delta_args) =
  let val P = (#1 o dest_comb o #1 o dest_eq o #2 o strip_forall o concl) RX_CURRENT_BD_PA_EQ_OR_ZERO_def in
  let val rd_delta_app = list_mk_comb (rd_delta, rd_delta_args) in
  let val P_app = mk_comb (P, rd_delta_app) in
  let val goal = list_mk_forall (List.rev rd_delta_args, P_app) in
    goal
  end end end end;

val rd_delta_preserves_or_clears_rx_current_bd_pa_goals =
  map create_rd_delta_preserves_or_clears_rx_current_bd_pa_goal rd_delta_def_args;

val RD_DELTA_PRESERVES_OR_CLEARS_RX_CURRENT_BD_PA_lemmas =
  let val goal_tactics =
    zip rd_delta_preserves_or_clears_rx_current_bd_pa_goals rd_delta_preserves_or_clears_rx_current_bd_pa_tacitcs in
  let val lemmas = map prove goal_tactics in
  let val rws =
    [RX_CURRENT_BD_PA_EQ_OR_ZERO_def,
     RX_CURRENT_BD_PA_EQ_def,
     RX_CURRENT_BD_PA_EQ_ZERO_def] in
    map (REWRITE_RULE rws) lemmas
  end end end;

val rd_transition_PRESERVES_OR_CLEARS_RX_CURRENT_BD_PA_lemma = store_thm (
  "rd_transition_PRESERVES_OR_CLEARS_RX_CURRENT_BD_PA_lemma",
  ``!nic env. RX_CURRENT_BD_PA_EQ_OR_ZERO nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_def] THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_ZERO_def] THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC RD_DELTA_PRESERVES_OR_CLEARS_RX_CURRENT_BD_PA_lemmas);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.rx.current_bd_pa*****************)
(******************************************************************************)





(******************************************************************************)
(*Start of lemmas regarding preservation of nic.rx.state***********************)
(******************************************************************************)

val RX_STATE_EQ_def = Define `
  RX_STATE_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.rx.state = nic'.rx.state)`;

(* Start of tactics solving goals of the form !nic env. RX_STATE_EQ nic (rd_<id><name> env nic) *)
val rd_0idle_rx_state_eq_tactic =
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic;

val rd_1_2_3_4_delta_rx_state_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  REPEAT (COND_CASES_TAC THENL
  [
   nic_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_5_6_delta_rx_state_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_delta_rx_state_eq_tactics =
  let fun get_rd_delta_tactics (i : int) =
    if i = 0 then 
      rd_0idle_rx_state_eq_tactic::get_rd_delta_tactics (i + 1)
    else if 1 <= i andalso i <= 4 then
      rd_1_2_3_4_delta_rx_state_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 5 then
      rd_5_6_delta_rx_state_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 6 then
      [rd_5_6_delta_rx_state_eq_tactic]
    else
      raise Fail "rd_delta_rx_state_eq_tactics: Index out of bounds."
  in
    get_rd_delta_tactics 0
  end;

(* End of tactics solving goals of the form !nic env. RX_STATE_EQ nic (rd_<id><name> env nic) *)

(* Given a transition function name and its arguments in reverse order, returns
   a term of the form !nic env. RX_STATE_EQ nic (rd_<id><name> env nic). *)

fun create_rd_delta_rx_state_eq_goal (rd_delta_args : term * term list) =
  let val P = (#1 o dest_comb o #1 o dest_eq o #2 o strip_forall o concl) RX_STATE_EQ_def in
  let val rd_delta_app = list_mk_comb rd_delta_args in
  let val P_args = mk_comb (P, rd_delta_app) in
  let val goal = list_mk_forall ((List.rev o #2) rd_delta_args, P_args) in
    goal
  end end end end;

val RD_DELTA_RX_STATE_EQ_lemmas =
  let val goals = map create_rd_delta_rx_state_eq_goal rd_delta_def_args in
  let val tactics = rd_delta_rx_state_eq_tactics in
  let val goal_tactics = zip goals tactics in
    map prove goal_tactics
  end end end;

val rd_transition_RX_STATE_EQ_lemma = store_thm (
  "rd_transition_RX_STATE_EQ_lemma",
  ``!nic env. RX_STATE_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC RD_DELTA_RX_STATE_EQ_lemmas);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.rx.state*************************)
(******************************************************************************)



(******************************************************************************)
(*Start of lemmas regarding preservation of nic.tx*****************************)
(******************************************************************************)

val TX_EQ_def = Define `
  TX_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.tx = nic'.tx)`;

val TX_EQ_SYM_lemma = store_thm (
  "TX_EQ_SYM_lemma",
  ``!nic nic'. TX_EQ nic nic' = TX_EQ nic' nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_EQ_def] THEN
  EQ_TAC THEN
  REWRITE_TAC [boolTheory.EQ_SYM]);

(* Start of tactics solving goals of the form !nic env. TX_EQ nic (rd_<id><name> env nic) *)
val rd_0idle_tx_eq_tactic =
  GEN_TAC THEN
  REWRITE_TAC [TX_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic;

val rd_1_2_3_4_delta_tx_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  REPEAT (COND_CASES_TAC THENL
  [
   nic_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_5_6_delta_tx_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_delta_tx_eq_tactics =
  let fun get_rd_delta_tactics (i : int) =
    if i = 0 then 
      rd_0idle_tx_eq_tactic::get_rd_delta_tactics (i + 1)
    else if 1 <= i andalso i <= 4 then
      rd_1_2_3_4_delta_tx_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 5 then
      rd_5_6_delta_tx_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 6 then
      [rd_5_6_delta_tx_eq_tactic]
    else
      raise Fail "rd_delta_tx_eq_tactics: Index out of bounds."
  in
    get_rd_delta_tactics 0
  end;

(* End of tactics solving goals of the form !nic env. TX_EQ nic (rd_<id><name> env nic) *)

(* Given a transition function name and its arguments in reverse order, returns
   a term of the form !nic env. TX_EQ nic (rd_<id><name> env nic). *)

fun create_rd_delta_tx_eq_goal (rd_delta_args : term * term list) =
  let val P = (#1 o dest_comb o #1 o dest_eq o #2 o strip_forall o concl) TX_EQ_def in
  let val rd_delta_app = list_mk_comb rd_delta_args in
  let val P_args = mk_comb (P, rd_delta_app) in
  let val goal = list_mk_forall ((List.rev o #2) rd_delta_args, P_args) in
    goal
  end end end end;

(* Theorems of the form:
  ``!nic. TX_EQ nic (rd_0idle nic)``,
  ``!nic env. TX_EQ nic (rd_1set_sop env nic)``,
  ``!nic env. TX_EQ nic (rd_2set_eop env nic)``,
  ``!nic env. TX_EQ nic (rd_3set_eoq env nic)``,
  ``!nic. TX_EQ nic (rd_4set_td nic)``,
  ``!nic. TX_EQ nic (rd_5clear_owner_and_hdp nic)``,
  ``!nic env. TX_EQ nic (rd_6write_cp env nic)``
 *)
val RD_DELTA_TX_EQ_lemmas =
  let val goals = map create_rd_delta_tx_eq_goal rd_delta_def_args in
  let val tactics = rd_delta_tx_eq_tactics in
  let val goal_tactics = zip goals tactics in
    map prove goal_tactics
  end end end;

val rd_transition_TX_EQ_lemma = store_thm (
  "rd_transition_TX_EQ_lemma",
  ``!nic env. TX_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC RD_DELTA_TX_EQ_lemmas);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.tx*******************************)
(******************************************************************************)





(******************************************************************************)
(*Start of lemmas regarding preservation of nic.tx.state***********************)
(******************************************************************************)

val TX_STATE_EQ_def = Define `
  TX_STATE_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.tx.state = nic'.tx.state)`;

val rd_transition_TX_STATE_EQ_lemma = store_thm (
  "rd_transition_TX_STATE_EQ_lemma",
  ``!nic env. TX_STATE_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_EQ_def] THEN
  ASSUME_TAC (SPEC_ALL (REWRITE_RULE [TX_EQ_def] rd_transition_TX_EQ_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_STATE_EQ_SYM_lemma = store_thm (
  "TX_STATE_EQ_SYM_lemma",
  ``!nic nic'. TX_STATE_EQ nic nic' = TX_STATE_EQ nic' nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_EQ_def] THEN
  EQ_TAC THEN
  REWRITE_TAC [boolTheory.EQ_SYM]);

val TX_STATE_EQ_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "TX_STATE_EQ_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic nic'.
    TX_STATE_EQ nic nic' /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_EQ_def] THEN
  ONCE_REWRITE_TAC [boolTheory.CONJ_COMM] THEN
  ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_DEP_lemma]);

val TX_STATE_EQ_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TX_STATE_EQ_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic nic'.
    TX_STATE_EQ nic nic' /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic
    ==>
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_EQ_def] THEN
  ONCE_REWRITE_TAC [boolTheory.CONJ_COMM] THEN
  ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
  REWRITE_TAC [TX_STATE_PROCESS_MEMORY_READ_REPLY_DEP_lemma]);

val TX_STATE_EQ_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "TX_STATE_EQ_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic nic'.
    TX_STATE_EQ nic nic' /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [TX_STATE_EQ_SYM_lemma] THEN
  REWRITE_TAC [TX_STATE_EQ_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma]);

val TX_STATE_EQ_REVERSE_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "TX_STATE_EQ_REVERSE_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic nic'.
    TX_STATE_EQ nic nic' /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic'
    ==>
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [TX_STATE_EQ_SYM_lemma] THEN
  REWRITE_TAC [TX_STATE_EQ_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma]);

val rd_transition_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "rd_transition_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TX_STATE_EQ_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma THEN
  Q.EXISTS_TAC `nic` THEN
  ASM_REWRITE_TAC [rd_transition_TX_STATE_EQ_lemma]);

val rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TX_STATE_EQ_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma THEN
  Q.EXISTS_TAC `nic'` THEN
  ASM_REWRITE_TAC [rd_transition_TX_STATE_EQ_lemma]);

val rd_transition_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "rd_transition_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic
    ==>
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TX_STATE_EQ_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma THEN
  Q.EXISTS_TAC `nic` THEN
  ASM_REWRITE_TAC [rd_transition_TX_STATE_EQ_lemma]);

val rd_transition_REVERSE_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic'
    ==>
    TX_STATE_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TX_STATE_EQ_REVERSE_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma THEN
  Q.EXISTS_TAC `nic'` THEN
  ASM_REWRITE_TAC [rd_transition_TX_STATE_EQ_lemma]);

val rd_transition_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "rd_transition_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_CASES_TAC ``TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_CASES_TAC ``TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'`` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_TX_STATE_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val rd_transition_EQ_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "rd_transition_EQ_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic)
    ==>
    (TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic' =
     TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  EQ_TAC THENL
  [
   DISCH_TAC THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   DISCH_TAC THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.tx.state*************************)
(******************************************************************************)



(******************************************************************************)
(*Start of lemmas regarding preservation of nic.tx.sop_bd_pa*******************)
(******************************************************************************)

val TX_SOP_BD_PA_EQ_def = Define `
  TX_SOP_BD_PA_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.tx.sop_bd_pa = nic'.tx.sop_bd_pa)`;

val rd_transition_TX_SOP_BD_PA_EQ_lemma = store_thm (
  "rd_transition_TX_SOPB_D_PA_EQ_lemma",
  ``!nic env. TX_SOP_BD_PA_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_SOP_BD_PA_EQ_def] THEN
  ASSUME_TAC (SPEC_ALL (REWRITE_RULE [TX_EQ_def] rd_transition_TX_EQ_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_SOP_BD_PA_EQ_SYM_lemma = store_thm (
  "TX_SOP_BD_PA_EQ_SYM_lemma",
  ``!nic nic'. TX_SOP_BD_PA_EQ nic nic' = TX_SOP_BD_PA_EQ nic' nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [TX_SOP_BD_PA_EQ_def] THEN
  EQ_TAC THEN
  REWRITE_TAC [boolTheory.EQ_SYM]);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.tx.sop_bd_pa*********************)
(******************************************************************************)



(******************************************************************************)
(*Start of lemmas regarding preservation of nic.regs.CPPI_RAM******************)
(******************************************************************************)

val CPPI_RAM_EQ_def = Define `
  CPPI_RAM_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.regs.CPPI_RAM = nic'.regs.CPPI_RAM)`;

val CPPI_RAM_EQ_SYM_lemma = store_thm (
  "CPPI_RAM_EQ_SYM_lemma",
  ``!nic nic'. CPPI_RAM_EQ nic nic' = CPPI_RAM_EQ nic' nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_EQ_def] THEN
  EQ_TAC THEN
  REWRITE_TAC [boolTheory.EQ_SYM]);

(* Given a transition function name and its arguments in reverse order, returns
   a term of the form
   !nic env.
   ~RD_WRITE_CURRENT_BD_PA nic
   ==>
   CPPI_RAM_EQ nic (rd_<id><name> env nic). *)
fun create_rd_delta_cppi_ram_eq_goal (rd_delta_args : term * term list) =
  let val ant = (mk_neg o #1 o dest_eq o #2 o dest_forall o concl) RD_WRITE_CURRENT_BD_PA_def in
  let val suc = (#1 o dest_comb o #1 o dest_eq o #2 o strip_forall o concl) CPPI_RAM_EQ_def in
  let val rd_delta_app = list_mk_comb rd_delta_args in
  let val suc_app = mk_comb (suc, rd_delta_app) in
  let val imp = mk_imp (ant, suc_app) in
  let val goal = list_mk_forall ((List.rev o #2) rd_delta_args, imp) in
    goal
  end end end end end end;

(* Start of tactics solving goals of the form !nic env. CPPI_RAM_EQ nic (rd_<id><name> env nic) *)
val rd_0idle_cppi_ram_eq_tactic =
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic;

val rd_1_2_3_4_delta_cppi_ram_eq_tactic =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [CPPI_RAM_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  COND_CASES_TAC THENL
  [
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``RD_WRITE_CURRENT_BD_PA nic`` ``~RD_WRITE_CURRENT_BD_PA nic`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_REWRITE_TAC [] THEN
   nic_with_rw_tactic THEN
   regs_with_rw_tactic
  ];

val rd_5_6_delta_cppi_ram_eq_tactic =
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [CPPI_RAM_EQ_def] THEN
  ASM_REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  regs_with_rw_tactic;

val rd_delta_cppi_ram_eq_tactics =
  let fun get_rd_delta_tactics (i : int) =
    if i = 0 then 
      rd_0idle_cppi_ram_eq_tactic::get_rd_delta_tactics (i + 1)
    else if 1 <= i andalso i <= 4 then
      rd_1_2_3_4_delta_cppi_ram_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 5 then
      rd_5_6_delta_cppi_ram_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 6 then
      [rd_5_6_delta_cppi_ram_eq_tactic]
    else
      raise Fail "rd_delta_cppi_ram_eq_tactics: Index out of bounds."
  in
    get_rd_delta_tactics 0
  end;

(* End of tactics solving goals of the form !nic env. CPPI_RAM_EQ nic (rd_<id><name> env nic) *)

(* Theorems of the form:
  ``!nic. CPPI_RAM_EQ nic (rd_0idle nic)``,
  ``!nic env. CPPI_RAM_EQ nic (rd_1set_sop env nic)``,
  ``!nic env. CPPI_RAM_EQ nic (rd_2set_eop env nic)``,
  ``!nic env. CPPI_RAM_EQ nic (rd_3set_eoq env nic)``,
  ``!nic. CPPI_RAM_EQ nic (rd_4set_td nic)``,
  ``!nic. CPPI_RAM_EQ nic (rd_5clear_owner_and_hdp nic)``,
  ``!nic env. CPPI_RAM_EQ nic (rd_6write_cp env nic)``
 *)
val RD_DELTA_CPPI_RAM_EQ_lemmas =
  let val goals = map create_rd_delta_cppi_ram_eq_goal rd_delta_def_args in
  let val tactics = rd_delta_cppi_ram_eq_tactics in
  let val goal_tactics = zip goals tactics in
    map prove goal_tactics
  end end end;

val rd_transition_CPPI_RAM_EQ_lemma = store_thm (
  "rd_transition_CPPI_RAM_EQ_lemma",
  ``!nic env.
    ~RD_WRITE_CURRENT_BD_PA nic
    ==>
    CPPI_RAM_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC RD_DELTA_CPPI_RAM_EQ_lemmas);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.regs.CPPI_RAM********************)
(******************************************************************************)





(******************************************************************************)
(*Start of lemmas regarding preservation of tx_bd_queue************************)
(******************************************************************************)

val rd_transition_NOT_WRITE_CURRENT_BD_PA_PRESERVES_TX_BD_QUEUE_lemma = store_thm (
  "rd_transition_NOT_WRITE_CURRENT_BD_PA_PRESERVES_TX_BD_QUEUE_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    ~RD_WRITE_CURRENT_BD_PA nic
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC EQ_SOP_BD_PA_AND_CPPI_RAM_AND_TX_INVARIANT_BD_QUEUE_FINITE_IMP_EQ_BD_QUEUES_lemma THEN
  ASSUME_TAC (GSYM (REWRITE_RULE [TX_SOP_BD_PA_EQ_def] (SPEC_ALL rd_transition_TX_SOP_BD_PA_EQ_lemma))) THEN
  ASSUME_TAC (UNDISCH (GSYM (REWRITE_RULE [CPPI_RAM_EQ_def] (SPEC_ALL rd_transition_CPPI_RAM_EQ_lemma)))) THEN
  ASM_REWRITE_TAC []);

val rd_transition_PRESERVES_TX_BD_QUEUE_CONTENTS_lemma = store_thm (
  "rd_transition_PRESERVES_TX_BD_QUEUE_CONTENTS_lemma",
  ``!nic env.
    BD_IN_CPPI_RAM nic.rx.current_bd_pa /\
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BD_NOT_OVERLAP_BDs nic.rx.current_bd_pa (tx_bd_queue nic)
    ==>
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM (rd_transition env nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``[nic.rx.current_bd_pa]`` THEN
  EXISTS_TAC ``rd_transition_cppi_ram_write_step_bd_pas env nic`` THEN
  REWRITE_TAC [rd_transition_WRITES_FIELDs_NOT_NDP_OF_BD_AT_CURRENT_BD_PA_lemma] THEN
  ASM_REWRITE_TAC [GSYM BD_IN_CPPI_RAM_EQ_BD_SINGLETON_IN_CPPI_RAM_lemma] THEN
  ASM_REWRITE_TAC [GSYM BD_NOT_OVERLAP_BDs_EQ_NO_BD_LIST_OVERLAP_lemma]);

val RX_CURRENT_BD_PA_NOT_OVERLAPPING_IMP_rd_transition_PRESERVES_TX_BD_QUEUE_lemma = store_thm (
  "RX_CURRENT_BD_PA_NOT_OVERLAPPING_IMP_rd_transition_PRESERVES_TX_BD_QUEUE_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM /\
    BD_IN_CPPI_RAM nic.rx.current_bd_pa /\
    BDs_IN_CPPI_RAM (tx_bd_queue nic) /\
    BD_NOT_OVERLAP_BDs nic.rx.current_bd_pa (tx_bd_queue nic)
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_PRESERVES_TX_BD_QUEUE_CONTENTS_lemma)) THEN
  ASSUME_TAC (REWRITE_RULE [TX_EQ_def] (SPEC_ALL rd_transition_TX_EQ_lemma)) THEN
  REFLECT_ASM_TAC ``nic' = rd_transition env nic`` THEN
  KEEP_ASM_RW_ASM_TAC ``f a0 a1 = (nic' : nic_state)`` ``(nic : nic_state).tx = (f a0 a1).tx`` THEN
  ASM_RW_ASM_TAC ``f a0 a1 = (nic' : nic_state)`` ``EQ_BDs q m m'`` THEN
  REFLECT_ASM_TAC ``(nic : nic_state).tx = nic'.tx`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val RD_INVARIANT_WRITE_CURRENT_BD_PA_IMP_IN_CPPI_RAM_NOT_OVERLAP_TX_BD_QUEUE_lemma = store_thm (
  "RD_INVARIANT_WRITE_CURRENT_BD_PA_IMP_IN_CPPI_RAM_NOT_OVERLAP_TX_BD_QUEUE_lemma",
  ``!nic.
    RD_INVARIANT nic /\
    RD_WRITE_CURRENT_BD_PA nic /\
    RX_STATE_IDLE nic /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic
    ==>
    BD_IN_CPPI_RAM nic.rx.current_bd_pa /\
    BD_NOT_OVERLAP_BDs nic.rx.current_bd_pa (tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RD_INVARIANT nic`` RD_INVARIANT_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RD_INVARIANT_CURRENT_BD_PA nic`` RD_INVARIANT_CURRENT_BD_PA_def THEN
  RW_ASM_TAC ``P ==> Q`` RD_STATE_WRITE_CPPI_RAM_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``RX_STATE_IDLE nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``RD_WRITE_CURRENT_BD_PA nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val rd_transition_WRITE_CURRENT_BD_PA_PRESERVES_TX_BD_QUEUE_lemma = store_thm (
  "rd_transition_WRITE_CURRENT_BD_PA_PRESERVES_TX_BD_QUEUE_lemma",
  ``!nic env nic' READABLE.
    (nic' = rd_transition env nic) /\
    RD_INVARIANT nic /\
    RD_WRITE_CURRENT_BD_PA nic /\
    RX_STATE_IDLE nic /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT nic READABLE
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_INVARIANT_WRITE_CURRENT_BD_PA_IMP_IN_CPPI_RAM_NOT_OVERLAP_TX_BD_QUEUE_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_IMP_TX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_INVARIANT_IMP_TX_BD_QUEUE_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_CURRENT_BD_PA_NOT_OVERLAPPING_IMP_rd_transition_PRESERVES_TX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);


  

val rd_transition_RD_TX_INVARIANTs_PRESERVES_TX_BD_QUEUE_lemma = store_thm (
  "rd_transition_RD_TX_INVARIANTs_PRESERVES_TX_BD_QUEUE_lemma",
  ``!nic env nic' READABLE.
    (nic' = rd_transition env nic) /\
    RD_INVARIANT nic /\
    RX_STATE_IDLE nic /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT nic READABLE
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_CASES_TAC ``RD_WRITE_CURRENT_BD_PA nic`` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_WRITE_CURRENT_BD_PA_PRESERVES_TX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_NOT_WRITE_CURRENT_BD_PA_PRESERVES_TX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val RD_AUTONOMOUS_TRANSITION_RD_TX_INVARIANTs_PRESERVE_TX_BD_QUEUE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_RD_TX_INVARIANTs_PRESERVE_TX_BD_QUEUE_lemma",
  ``!nic env nic' READABLE.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT nic /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic /\
    TX_INVARIANT nic READABLE
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_RD_TX_INVARIANTs_PRESERVES_TX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(******************************************************************************)
(*End of lemmas regarding preservation of tx_bd_queue**************************)
(******************************************************************************)




(******************************************************************************)
(*Start of lemmas regarding preservation of the antecedent of RD_INVARIANT*****)
(******************************************************************************)

val rd_transition_REVERSE_PRESERVES_RX_STATE_IDLE_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_RX_STATE_IDLE_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    RX_STATE_IDLE nic'
    ==>
    RX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``nic' : nic_state = f a0 f1`` ``nic' : nic_state.rx.state = rx_idle`` THEN
  RW_ASM_TAC ``P`` (GSYM (REWRITE_RULE [RX_STATE_EQ_def] rd_transition_RX_STATE_EQ_lemma)) THEN
  ASM_REWRITE_TAC []);

val rd_transition_REVERSE_PRESERVES_RD_WRITE_CURRENT_BD_PA_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_RD_WRITE_CURRENT_BD_PA_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    RD_WRITE_CURRENT_BD_PA nic'
    ==>
    RD_WRITE_CURRENT_BD_PA nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_CURRENT_BD_PA_EQ_OR_ZERO_REVERSE_PRESERVES_RD_WRITE_CURRENT_BD_PA_lemma THEN
  Q.EXISTS_TAC `nic'` THEN
  ASM_REWRITE_TAC [rd_transition_PRESERVES_OR_CLEARS_RX_CURRENT_BD_PA_lemma]);

val rd_transition_REVERSE_PRESERVES_RD_STATE_WRITE_CPPI_RAM_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_RD_STATE_WRITE_CPPI_RAM_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    RD_STATE_WRITE_CPPI_RAM nic'
    ==>
    RD_STATE_WRITE_CPPI_RAM nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_STATE_WRITE_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_RX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_RD_WRITE_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC []);

val rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'
    ==>
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rd_transition_EQ_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_RW_ASM_TAC ``f a = f b`` ``f a`` THEN
  ASM_REWRITE_TAC []);

val rd_transition_REVERSE_PRESERVES_RD_INVARIANT_ANTECEDENT_lemma = store_thm (
  "rd_transition_REVERSE_PRESERVES_RD_INVARIANT_ANTECEDENT_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    RD_STATE_WRITE_CPPI_RAM nic' /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic'
    ==>
    RD_STATE_WRITE_CPPI_RAM nic /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_RD_STATE_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY_lemma)) THEN
  ASM_REWRITE_TAC []);

(******************************************************************************)
(*End of lemmas regarding preservation of the antecedent of RD_INVARIANT*******)
(******************************************************************************)




(******************************************************************************)
(*Start of lemmas regarding preservation of RD_INVARIANT_CURRENT_BD_PA*********)
(******************************************************************************)

val RX_CURRENT_BD_PA_EQ_ZERO_IMP_RD_INVARIANT_CURRENT_BD_PA_lemma = store_thm (
  "RX_CURRENT_BD_PA_EQ_ZERO_IMP_RD_INVARIANT_CURRENT_BD_PA_lemma",
  ``!nic.
    RX_CURRENT_BD_PA_EQ_ZERO nic
    ==>
    RD_INVARIANT_CURRENT_BD_PA nic``,
  GEN_TAC THEN
  REWRITE_TAC [RX_CURRENT_BD_PA_EQ_ZERO_def] THEN
  DISCH_TAC THEN
  REWRITE_TAC [RD_INVARIANT_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RD_WRITE_CURRENT_BD_PA_def] THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_CURRENT_BD_PA_EQ_PRESERVES_RD_INVARIANT_CURRENT_BD_PA_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_CURRENT_BD_PA_EQ_PRESERVES_RD_INVARIANT_CURRENT_BD_PA_lemma",
  ``!nic env nic' READABLE.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RX_CURRENT_BD_PA_EQ nic nic' /\
    RD_INVARIANT nic /\
    TX_INVARIANT nic READABLE
    ==>
    RD_INVARIANT_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [RD_INVARIANT_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  RW_KEEP_ASM_TAC ``RD_INVARIANT nic`` RD_INVARIANT_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rd_transition_REVERSE_PRESERVES_RD_INVARIANT_ANTECEDENT_lemma)) THEN
  RW_KEEP_ASM_TAC ``RD_INVARIANT_CURRENT_BD_PA nic`` RD_INVARIANT_CURRENT_BD_PA_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  RW_ASM_TAC ``RX_CURRENT_BD_PA_EQ nic nic'`` RX_CURRENT_BD_PA_EQ_def THEN
  PAT_ASSUM ``nic'.rx.current_bd_pa = nic.rx.current_bd_pa`` (fn thm => REWRITE_TAC [thm]) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_RD_TX_INVARIANTs_PRESERVE_TX_BD_QUEUE_lemma)) THEN
  PAT_ASSUM ``tx_bd_queue nic' = tx_bd_queue nic`` (fn thm => REWRITE_TAC [thm]) THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_CURRENT_BD_PA_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_CURRENT_BD_PA_lemma",
  ``!nic env nic' READABLE.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT nic /\
    TX_INVARIANT nic READABLE
    ==>
    RD_INVARIANT_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_CASES_TAC ``RX_CURRENT_BD_PA_EQ_ZERO nic'`` THENL
  [
   MATCH_MP_TAC RX_CURRENT_BD_PA_EQ_ZERO_IMP_RD_INVARIANT_CURRENT_BD_PA_lemma THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
   KEEP_ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
   ASSUME_TAC (REWRITE_RULE [RX_CURRENT_BD_PA_EQ_OR_ZERO_def] (SPEC_ALL rd_transition_PRESERVES_OR_CLEARS_RX_CURRENT_BD_PA_lemma)) THEN
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   REFLECT_ASM_TAC ``x = y`` THEN
   ASM_RW_ASM_TAC ``x = y`` ``RX_CURRENT_BD_PA_EQ nic (rd_transition env nic)`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_CURRENT_BD_PA_EQ_PRESERVES_RD_INVARIANT_CURRENT_BD_PA_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(******************************************************************************)
(*End of lemmas regarding preservation of RD_INVARIANT_CURRENT_BD_PA***********)
(******************************************************************************)

(******************************************************************************)
(*Start of lemmas regarding preservation of RD_INVARIANT_RD_CLEARS_BD_QUEUE****)
(******************************************************************************)

val rd_delta_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemmas = [
  rd_0idle_RD_STATE_IDLE_IMP_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma,
  rd_1set_sop_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma,
  rd_2set_eop_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma,
  rd_3set_eoq_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma,
  rd_4set_td_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma,
  rd_5clear_owner_and_hdp_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma,
  rd_6write_cp_ESTABLISHES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma];

val RD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RD_INVARIANT_RD_CLEARS_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASSUME_TAC (SPEC_ALL RD_STATE_CASES_lemma) THEN
  let fun t (rd_id : int) =
    let val rd_delta_eq_lemma =
      rdLib.get_rd_conjunct RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_CONJ_lemmas rd_id in
    let val clear_lemma = List.nth (rd_delta_RD_INVARIANT_RD_CLEARS_BD_QUEUE_lemmas, rd_id) in
      ASSUME_TAC (UNDISCH (SPEC_ALL rd_delta_eq_lemma)) THEN
      ASM_RW_ASM_TAC ``rd_transition nic env = x`` ``y = rd_transition env nic`` THEN
      ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL clear_lemma)) THEN
      ASM_REWRITE_TAC []
    end end
  in
    REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
      let val left = (#1 o dest_disj o concl) thm in
        ASM_CASES_TAC left THENL
        [
         let val rd_id = rdLib.rd_transition_state_application_to_rd_id left in t rd_id end
         ,
         ASSUME_TAC thm THEN
         ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
        ]
      end)) THEN
    t 6
  end);

(******************************************************************************)
(*End of lemmas regarding preservation of RD_INVARIANT_RD_CLEARS_BD_QUEUE******)
(******************************************************************************)


(******************************************************************************)
(*Start of lemmas regarding preservation of RD_INVARIANT_RX_ADVANCES_BD_QUEUE**)
(******************************************************************************)

val NOT_RD_STATE_WRITE_CP_OR_RX_SOP_BD_PA_EQ_ZERO_AND_RX_STATE_IDLE_IMP_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma = store_thm (
  "NOT_RD_STATE_WRITE_CP_OR_RX_SOP_BD_PA_EQ_ZERO_AND_RX_STATE_IDLE_IMP_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma",
  ``!nic.
    ~RD_STATE_WRITE_CP nic \/ ((nic.rx.sop_bd_pa = 0w) /\ RX_STATE_IDLE nic)
    ==>
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic``,
  GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_RX_ADVANCES_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  ASM_CASES_TAC ``~RD_STATE_WRITE_CP nic`` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   RW_ASM_TAC ``RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`` RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def THEN
   RW_ASM_TAC ``RX_ENABLE nic`` schedulerTheory.RX_ENABLE_def THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``RX_STATE_IDLE nic`` RX_STATE_IDLE_def THEN
   ASM_RW_ASM_TAC ``nic.rx.sop_bd_pa = 0w`` ``P \/ Q`` THEN
   ASM_RW_ASM_TAC ``x = y`` ``x <> y`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val rd_delta_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemmas = [
  rd_0idle_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma,
  rd_1set_sop_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma,
  rd_2set_eop_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma,
  rd_3set_eoq_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma,
  rd_4set_td_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma,
  rd_5clear_owner_and_hdp_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma,
  rd_6write_cp_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemma];

val rd_delta_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemmas =
  map
  (fn imp1 => GEN_ALL (IMP_TRANS (SPEC_ALL imp1) (SPEC ``nic' : nic_state`` NOT_RD_STATE_WRITE_CP_OR_RX_SOP_BD_PA_EQ_ZERO_AND_RX_STATE_IDLE_IMP_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma)))
  rd_delta_NEXT_STATE_NOT_RD_WRITE_CP_OR_CLEAR_RX_SOP_BD_PA_AND_NEXT_STATE_RX_IDLE_lemmas;

val RD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_PRESERVES_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RD_INVARIANT_RX_ADVANCES_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_ENABLE_lemma)) THEN
  ASSUME_TAC (SPEC_ALL RD_STATE_CASES_lemma) THEN
  let fun t (rd_id : int) =
    let val rd_delta_eq_lemma =
      rdLib.get_rd_conjunct RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_CONJ_lemmas rd_id in
    let val inv_lemma = List.nth (rd_delta_RD_INVARIANT_RX_ADVANCES_BD_QUEUE_lemmas, rd_id) in
      ASSUME_TAC (UNDISCH (SPEC_ALL rd_delta_eq_lemma)) THEN
      ASM_RW_ASM_TAC ``rd_transition nic env = x`` ``y = rd_transition env nic`` THEN
      ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL inv_lemma)) THEN
      ASM_REWRITE_TAC []
    end end
  in
    REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
      let val left = (#1 o dest_disj o concl) thm in
        ASM_CASES_TAC left THENL
        [
         let val rd_id = rdLib.rd_transition_state_application_to_rd_id left in t rd_id end
         ,
         ASSUME_TAC thm THEN
         ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
        ]
      end)) THEN
    t 6
  end);

(******************************************************************************)
(*End of lemmas regarding preservation of RD_INVARIANT_RX_ADVANCES_BD_QUEUE****)
(******************************************************************************)




(******************************************************************************)
(*Start of lemmas regarding preservation of dead*******************************)
(******************************************************************************)

val DEAD_EQ_def = Define `
  DEAD_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.dead = nic'.dead)`;

val DEAD_EQ_SYM_lemma = store_thm (
  "DEAD_EQ_SYM_lemma",
  ``!nic nic'. DEAD_EQ nic nic' = DEAD_EQ nic' nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DEAD_EQ_def] THEN
  EQ_TAC THEN
  REWRITE_TAC [boolTheory.EQ_SYM]);

(* Given a transition function name and its arguments in reverse order, returns
   a term of the form !nic env. DEAD_EQ nic (rd_<id><name> env nic). *)

fun create_rd_delta_dead_eq_goal (rd_delta_args : term * term list) =
  let val P = (#1 o dest_comb o #1 o dest_eq o #2 o strip_forall o concl) DEAD_EQ_def in
  let val rd_delta_app = list_mk_comb rd_delta_args in
  let val P_args = mk_comb (P, rd_delta_app) in
  let val goal = list_mk_forall ((List.rev o #2) rd_delta_args, P_args) in
    goal
  end end end end;

(* Start of tactics solving goals of the form !nic env. DEAD_EQ nic (rd_<id><name> env nic) *)
val rd_1_2_3_4_delta_dead_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DEAD_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  REPEAT (COND_CASES_TAC THENL
  [
   nic_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_5_6_delta_dead_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DEAD_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_delta_dead_eq_tactics =
  let fun get_rd_delta_tactics (i : int) =
    if 1 <= i andalso i <= 4 then
      rd_1_2_3_4_delta_dead_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 5 then
      rd_5_6_delta_dead_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 6 then
      [rd_5_6_delta_dead_eq_tactic]
    else
      raise Fail "rd_delta_dead_eq_tactics: Index out of bounds."
  in
    get_rd_delta_tactics 1
  end;

(* End of tactics solving goals of the form !nic env. DEAD_EQ nic (rd_<id><name> env nic) *)

(* Theorems of the form:
  ``!nic env. DEAD_EQ nic (rd_1set_sop env nic)``,
  ``!nic env. DEAD_EQ nic (rd_2set_eop env nic)``,
  ``!nic env. DEAD_EQ nic (rd_3set_eoq env nic)``,
  ``!nic. DEAD_EQ nic (rd_4set_td nic)``,
  ``!nic. DEAD_EQ nic (rd_5clear_owner_and_hdp nic)``,
  ``!nic env. DEAD_EQ nic (rd_6write_cp env nic)``
 *)
val RD_DELTA_DEAD_EQ_lemmas =
  let val goals = map create_rd_delta_dead_eq_goal (tl rd_delta_def_args) in
  let val tactics = rd_delta_dead_eq_tactics in
  let val goal_tactics = zip goals tactics in
    map prove goal_tactics
  end end end;

val RD_STATE_NOT_IDLE_IMP_NOT_RD_STATE_IDLE_lemma = store_thm (
  "RD_STATE_NOT_IDLE_IMP_NOT_RD_STATE_IDLE_lemma",
  ``!nic.
    RD_STATE_NOT_IDLE nic
    ==>
    ~RD_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_STATE_NOT_IDLE_def] THEN
  REWRITE_TAC [RD_STATE_SET_SOP_def] THEN
  REWRITE_TAC [RD_STATE_SET_EOP_def] THEN
  REWRITE_TAC [RD_STATE_SET_EOQ_def] THEN
  REWRITE_TAC [RD_STATE_SET_TD_def] THEN
  REWRITE_TAC [RD_STATE_CLEAR_OWNER_AND_HDP_def] THEN
  REWRITE_TAC [RD_STATE_WRITE_CP_def] THEN
  REWRITE_TAC [RD_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [GSYM stateTheory.rd_abstract_state_distinct] THEN
  RW_ASM_TAC ``P \/ Q`` stateTheory.rd_abstract_state_distinct THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val rd_transition_DEAD_EQ_lemma = store_thm (
  "rd_transition_DEAD_EQ_lemma",
  ``!nic env.
    RD_STATE_NOT_IDLE nic
    ==>
    DEAD_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_STATE_NOT_IDLE_IMP_NOT_RD_STATE_IDLE_lemma)) THEN
  RW_ASM_TAC ``~P`` RD_STATE_IDLE_def THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC RD_DELTA_DEAD_EQ_lemmas THEN
  RW_ASM_TAC ``~P`` (SPEC ``rd_idle`` (INST_TYPE [alpha |-> ``:rd_abstract_state``] boolTheory.EQ_REFL)) THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val rd_transition_RD_STATE_NOT_IDLE_PRESERVES_DEAD_lemma = store_thm (
  "rd_transition_RD_STATE_NOT_IDLE_PRESERVES_DEAD_lemma",
  ``!nic env nic'.
    (nic' = rd_transition env nic) /\
    RD_STATE_NOT_IDLE nic
    ==>
    (nic'.dead = nic.dead)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``x = y`` (fn thm => REWRITE_TAC [thm]) THEN
  ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
  REWRITE_TAC [GSYM DEAD_EQ_def] THEN
  MATCH_MP_TAC rd_transition_DEAD_EQ_lemma THEN
  ASM_REWRITE_TAC []);

(******************************************************************************)
(*End of lemmas regarding preservation of dead*********************************)
(******************************************************************************)


(******************************************************************************)
(*Start of lemmas regarding current state being write_cp if next state is idle*)
(******************************************************************************)

val NOT_NEXT_RD_STATE_IDLE_lemmas = [
  boolTheory.TRUTH,
  rd_1set_sop_IMP_NOT_NEXT_RD_STATE_IDLE_lemma,
  rd_2set_eop_IMP_NOT_NEXT_RD_STATE_IDLE_lemma,
  rd_3set_eoq_IMP_NOT_NEXT_RD_STATE_IDLE_lemma,
  rd_4set_td_IMP_NOT_NEXT_RD_STATE_IDLE_lemma,
  rd_5clear_owner_and_hdp_IMP_NOT_NEXT_RD_STATE_IDLE_lemma,
  boolTheory.TRUTH];

val RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_IMP_RD_STATE_WRITE_CP_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_IMP_RD_STATE_WRITE_CP_lemma",
  ``!nic env nic' WRITABLE.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_STATE_IDLE nic'
    ==>
    RD_STATE_WRITE_CP nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RD_ENABLE_def] THEN
  REWRITE_TAC [rd_transition_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  (* First tactic of ORELSE solves the first subgoal, and the third tactic solves
     the last subgoal and the second tactic solves the other subgoals. NO_TAC fails
     and causes the respective tactic of ORELSE to fail unless it solves the goal. *)
  Cases_on `nic.rd.state` THEN
  (
   (RW_ASM_TAC ``x <> x`` (INST_TYPE [alpha |-> ``: rd_abstract_state``] boolTheory.EQ_REFL) THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC [] THEN
    NO_TAC
   )
   ORELSE
   (
    RW_ASM_TAC ``nic' = rd_transition_case a0 a1 a2`` rd_transition_case_def THEN
    RW_ASM_TAC ``nic.rd.state = x`` (GSYM rdLib.RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws) THEN
    PAT_ASSUM ``f a`` (fn thm =>
      let val rd_id = rdLib.rd_transition_state_application_to_rd_id (concl thm) in
      let val lemma = List.nth (NOT_NEXT_RD_STATE_IDLE_lemmas, rd_id) in
        ASSUME_TAC (UNDISCH (SPEC_ALL lemma))
      end end) THEN
    ASM_RW_ASM_TAC ``~(f a)`` ``RD_STATE_IDLE nic'`` THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC [] THEN
    NO_TAC
   )
   ORELSE
   (
    ASM_REWRITE_TAC [RD_STATE_WRITE_CP_def]
   )
  ));

(******************************************************************************)
(*End of lemmas regarding current state being write_cp if next state is idle***)
(******************************************************************************)

val RD_AUTONOMOUS_TRANSITION_IMP_NOT_RD_STATE_IDLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_NOT_RD_STATE_IDLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    ~RD_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RD_ENABLE_def] THEN
  REWRITE_TAC [RD_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RX_STATE_IDLE nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RD_ENABLE_def] THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_IMP_NEXT_RX_STATE_IDLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_IMP_NEXT_RX_STATE_IDLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic'
    ==>
    RX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RX_STATE_IDLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  RW_ASM_TAC ``RX_STATE_IDLE nic`` RX_STATE_IDLE_def THEN
  REWRITE_TAC [GSYM (REWRITE_RULE [RX_STATE_EQ_def] (SPEC_ALL rd_transition_RX_STATE_EQ_lemma))] THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_NOT_NEXT_RD_STATE_IDLE_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_NOT_NEXT_RD_STATE_IDLE_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    ~RD_STATE_IDLE nic'
    ==>
    ~RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RD_ENABLE_def] THEN
  REWRITE_TAC [RD_STATE_IDLE_def] THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RX_ENABLE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC [] THEN
  REFLECT_ASM_TAC ``nic.rx.state = rx_idle`` THEN
  ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [GSYM (REWRITE_RULE [RX_STATE_EQ_def] rd_transition_RX_STATE_EQ_lemma)] THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_RD_STATE_IDLE_PRESERVES_RX_SOP_BD_PA_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_RD_STATE_IDLE_PRESERVES_RX_SOP_BD_PA_lemma",
  ``!nic env nic' WRITABLE.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_STATE_IDLE nic'
    ==>
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_IMP_RD_STATE_WRITE_CP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (rdLib.get_rd_conjunct RD_STATE_TRANSITION_IMP_RD_TRANSITION_STEP_EQ_CONJ_lemmas 6))) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_RD_TRANSITION_lemma)) THEN
  ASM_RW_ASM_TAC ``rd_transition env nic = t`` ``nic' = rd_transition env nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rd_6write_cp_NOT_MODIFIED_lemma)) THEN
  ASM_REWRITE_TAC []);

val RD_STATE_WRITE_CP_RD_INVARIANT_IMP_RX_SOP_BD_PA_EQ_ZERO_lemma = store_thm (
  "RD_STATE_WRITE_CP_RD_INVARIANT_IMP_RX_SOP_BD_PA_EQ_ZERO_lemma",
  ``!nic env nic' WRITABLE.
    RD_STATE_WRITE_CP nic /\
    RD_INVARIANT nic
    ==>
    (nic.rx.sop_bd_pa = 0w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RD_INVARIANT_def] THEN
  REWRITE_TAC [RD_INVARIANT_RD_CLEARS_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_RD_STATE_IDLE_RD_INVARIANT_IMP_NEXT_RX_SOP_BD_PA_EQ_ZERO_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_RD_STATE_IDLE_RD_INVARIANT_IMP_NEXT_RX_SOP_BD_PA_EQ_ZERO_lemma",
  ``!nic env nic' WRITABLE.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_STATE_IDLE nic' /\
    RD_INVARIANT nic
    ==>
    (nic'.rx.sop_bd_pa = 0w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_RD_STATE_IDLE_PRESERVES_RX_SOP_BD_PA_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_IMP_RD_STATE_WRITE_CP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_STATE_WRITE_CP_RD_INVARIANT_IMP_RX_SOP_BD_PA_EQ_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_RD_INVARIANT_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_RD_INVARIANT_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_STATE_IDLE nic' /\
    RD_INVARIANT nic
    ==>
    ~RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RX_ENABLE_def] THEN
  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_RD_STATE_IDLE_RD_INVARIANT_IMP_NEXT_RX_SOP_BD_PA_EQ_ZERO_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RD_AUTONOMOUS_TRANSITION_IMP_NEXT_RX_STATE_IDLE_lemma)) THEN
  RW_ASM_TAC ``RX_STATE_IDLE nic'`` RX_STATE_IDLE_def THEN
  ASM_REWRITE_TAC []);

val RD_AUTONOMOUS_TRANSITION_RD_INVARIANT_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "RD_AUTONOMOUS_TRANSITION_RD_INVARIANT_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic'.
    RD_AUTONOMOUS_TRANSITION nic env nic' /\
    RD_INVARIANT nic
    ==>
    ~RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic'``,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_CASES_TAC ``RD_STATE_IDLE nic'`` THENL
   [
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_NEXT_RD_STATE_IDLE_RD_INVARIANT_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
    ASM_REWRITE_TAC []
    ,
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RD_AUTONOMOUS_TRANSITION_NOT_NEXT_RD_STATE_IDLE_IMP_NOT_NEXT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
    ASM_REWRITE_TAC []
   ]);

(******************************************************************************)
(*Start of lemmas regarding preservation of nic.it*****************************)
(******************************************************************************)

val IT_EQ_def = Define `
  IT_EQ (nic : nic_state) (nic' : nic_state) =
  (nic.it = nic'.it)`;

val IT_EQ_SYM_lemma = store_thm (
  "IT_EQ_SYM_lemma",
  ``!nic nic'. IT_EQ nic nic' = IT_EQ nic' nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_EQ_def] THEN
  EQ_TAC THEN
  REWRITE_TAC [boolTheory.EQ_SYM]);

(* Start of tactics solving goals of the form !nic env. IT_EQ nic (rd_<id><name> env nic) *)
val rd_0idle_it_eq_tactic =
  GEN_TAC THEN
  REWRITE_TAC [IT_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic;

val rd_1_2_3_4_delta_it_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  REPEAT (COND_CASES_TAC THENL
  [
   nic_with_rw_tactic
   ,
   ALL_TAC
  ]) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_5_6_delta_it_eq_tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_EQ_def] THEN
  REWRITE_TAC rd_delta_defs THEN
  nic_with_rw_tactic THEN
  rx_with_rw_tactic;

val rd_delta_it_eq_tactics =
  let fun get_rd_delta_tactics (i : int) =
    if i = 0 then 
      rd_0idle_it_eq_tactic::get_rd_delta_tactics (i + 1)
    else if 1 <= i andalso i <= 4 then
      rd_1_2_3_4_delta_it_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 5 then
      rd_5_6_delta_it_eq_tactic::get_rd_delta_tactics (i + 1)
    else if i = 6 then
      [rd_5_6_delta_it_eq_tactic]
    else
      raise Fail "rd_delta_it_eq_tactics: Index out of bounds."
  in
    get_rd_delta_tactics 0
  end;

(* End of tactics solving goals of the form !nic env. IT_EQ nic (rd_<id><name> env nic) *)

(* Given a transition function name and its arguments in reverse order, returns
   a term of the form !nic env. IT_EQ nic (rd_<id><name> env nic). *)

fun create_rd_delta_it_eq_goal (rd_delta_args : term * term list) =
  let val P = (#1 o dest_comb o #1 o dest_eq o #2 o strip_forall o concl) IT_EQ_def in
  let val rd_delta_app = list_mk_comb rd_delta_args in
  let val P_args = mk_comb (P, rd_delta_app) in
  let val goal = list_mk_forall ((List.rev o #2) rd_delta_args, P_args) in
    goal
  end end end end;

(* Theorems of the form:
  ``!nic. IT_EQ nic (rd_0idle nic)``,
  ``!nic env. IT_EQ nic (rd_1set_sop env nic)``,
  ``!nic env. IT_EQ nic (rd_2set_eop env nic)``,
  ``!nic env. IT_EQ nic (rd_3set_eoq env nic)``,
  ``!nic. IT_EQ nic (rd_4set_td nic)``,
  ``!nic. IT_EQ nic (rd_5clear_owner_and_hdp nic)``,
  ``!nic env. IT_EQ nic (rd_6write_cp env nic)``
 *)
val RD_DELTA_IT_EQ_lemmas =
  let val goals = map create_rd_delta_it_eq_goal rd_delta_def_args in
  let val tactics = rd_delta_it_eq_tactics in
  let val goal_tactics = zip goals tactics in
    map prove goal_tactics
  end end end;

val rd_transition_IT_EQ_lemma = store_thm (
  "rd_transition_IT_EQ_lemma",
  ``!nic env. IT_EQ nic (rd_transition env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rd_transition_def] THEN
  Cases_on `nic.rd.state` THEN
  REWRITE_TAC [rd_transition_case_def] THEN
  REWRITE_TAC RD_DELTA_IT_EQ_lemmas);

(******************************************************************************)
(*End of lemmas regarding preservation of nic.it*******************************)
(******************************************************************************)

val _ = export_theory();

