open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxTheory;
open rx_transition_definitionsTheory;
open rx_state_definitionsTheory;
open schedulerTheory;
open it_state_definitionsTheory;
open rx_state_lemmasTheory;

val _ = new_theory "rx_transition_lemmas";

val nic_rw =
  nic_rw_tactics.rw_state_tactic
  `nic`
  [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors];

val rx_rw =
  nic_rw_tactics.rw_state_tactic
  `r`
  [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors];

(* This theory contains definitions and lemmas related to the top-level rx
   transition function. *)

(* Generates terms of the following form:
   !nic env.
   RX_STATE_RECEIVE_FRAME nic
   ==>
   (rx_transition env nic = (rx_0receive_new_frame env nic, NONE))*)
fun generate_rx_state_imp_rx_transition_eq (rx_id : int) =
  let val ant = rxLib.rx_id_to_rx_transition_state_application rx_id in
  let val leq = ``rx_transition env nic`` in
  let val req = rxLib.rx_id_to_rx_transition_function_application rx_id in
  let val suc = mk_eq (leq, req) in
  let val imp = mk_imp (ant, suc) in
  mk_forall (``nic : nic_state``, mk_forall (``env : environment``, imp))
  end end end end end;

fun prove_rx_state_imp_rx_transition_eq (rx_id : int) = prove (
  generate_rx_state_imp_rx_transition_eq rx_id,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rxLib.RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_CASES_CONJ_rws] THEN
  REWRITE_TAC rxLib.RX_STATE_defs THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_transition_def, stateTheory.rx_abstract_state_case_def]);

fun prove_rx_state_imp_rx_transition_eqs 19    = [prove_rx_state_imp_rx_transition_eq 19]
  | prove_rx_state_imp_rx_transition_eqs rx_id = (prove_rx_state_imp_rx_transition_eq rx_id)::(prove_rx_state_imp_rx_transition_eqs (rx_id + 1));

(* Generates a theorem consisting of conjuncts of the following form:
   !nic v.
   TX_STATE_IDLE_INIT_NOT_BD_QUEUE_EMPTY nic
   ==>
   (tx_transition nic v = (tx_0receive_new_frame nic v.received_frame, NONE))*)
val RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_lemmas = prove_rx_state_imp_rx_transition_eqs 0;

val RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas = save_thm (
  "RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas",
  LIST_CONJ RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_lemmas);

val RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic``,
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val RX_AUTONOMOUS_TRANSITION_IMP_NOT_RX_STATE_IDLE_OR_IT_STATE_INITIALIZED_NOT_RX_BD_QUEUE_EMPTY_RD_STATE_IDLE_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_IMP_NOT_RX_STATE_IDLE_OR_IT_STATE_INITIALIZED_NOT_RX_BD_QUEUE_EMPTY_RD_STATE_IDLE_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    ~RX_STATE_IDLE nic \/
    (IT_STATE_INITIALIZED nic /\ ~RX_BD_QUEUE_EMPTY nic /\ RD_STATE_IDLE nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  PAT_ASSUM ``RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM boolTheory.NOT_CLAUSES] thm)) THEN
  PAT_ASSUM ``~~P`` (fn thm => ASSUME_TAC (PURE_REWRITE_RULE [SPEC_ALL NOT_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_EQ_RX_STATE_IDLE_NOT_IT_STATE_INITIALIZED_OR_RX_BD_QUEUE_EMPTY_OR_NOT_RD_STATE_IDLE_lemma] thm)) THEN
  RW_ASM_TAC ``~P`` boolTheory.DE_MORGAN_THM THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_IMP_RX_TRANSITION_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_IMP_RX_TRANSITION_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    ((nic',mr') = rx_transition env nic)``,
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val rx_transition_FST_SND_EQ_lemma = store_thm (
  "rx_transition_FST_SND_EQ_lemma",
  ``!nic env.
    (FST (rx_transition env nic), SND (rx_transition env nic)) = rx_transition env nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pairTheory.PAIR]);








val rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_RD_REGS_PRESERVED_lemma = store_thm (
  "rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_RD_REGS_PRESERVED_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic)
    ==>
    ~RX_STATE_IDLE nic' \/ ((nic'.tx = nic.tx) /\ (nic'.rx = nic.rx) /\ (nic'.rd = nic.rd) /\ (nic'.regs = nic.regs))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   nic_rw_tactics.rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors]
   ,
   ALL_TAC
  ] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  COND_CASES_TAC THENL
  [
   DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   nic_rw_tactics.rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors]
   ,
   ALL_TAC
  ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn _ => true)) THEN
  nic_rw_tactics.rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  nic_rw_tactics.rw_state_tactic `r` [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
  REWRITE_TAC [REWRITE_RULE [DECIDE ``2 < 20 : num``, DECIDE ``0 < 20 : num``] (SPECL [``2 : num``, ``0 : num``] stateTheory.num2rx_abstract_state_11)] THEN
  DECIDE_TAC);

val rx_0receive_new_frame_NEXT_STATE_NOT_IDLE_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma = store_thm (
  "rx_0receive_new_frame_NEXT_STATE_NOT_IDLE_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic)
    ==>
    ~RX_STATE_IDLE nic' \/
    ((nic'.tx = nic.tx) /\
     (nic'.rx.state = nic.rx.state) /\ (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\ (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
     (nic'.rd = nic.rd) /\
     (nic'.regs = nic.regs))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_0receive_new_frame_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``P`` (fn thm =>
    let val (post, rhs) = (dest_eq o concl) thm in
    let val inter = (#2 o dest_comb) rhs in
      ASSUME_TAC (UNDISCH (SPECL [inter, post] rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_RD_REGS_PRESERVED_lemma))
    end end) THEN
  ASM_CASES_TAC ``~RX_STATE_IDLE nic'`` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~~P`` ``~P \/ Q`` THEN
   ASM_REWRITE_TAC [] THEN
   nic_rw_tactics.rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
   nic_rw_tactics.rw_state_tactic `r` [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors]
  ]);

val rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic) /\
    RX_STATE_FETCH_NEXT_BD nic
    ==>
    ~RX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_OR_TX_RX_RD_REGS_PRESERVED_lemma)) THEN
  ASM_CASES_TAC ``~RX_STATE_IDLE nic'`` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~~P`` ``~P \/ Q`` THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD nic`` RX_STATE_FETCH_NEXT_BD_def THEN
   ASM_REWRITE_TAC [RX_STATE_IDLE_def] THEN
   REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
   REWRITE_TAC [REWRITE_RULE [DECIDE ``1 < 20 : num``, DECIDE ``0 < 20 : num``] (SPECL [``1 : num``, ``0 : num``] stateTheory.num2rx_abstract_state_11)] THEN
   DECIDE_TAC
  ]);

val rx_2issue_next_memory_write_request_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "rx_2issue_next_memory_write_request_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    ~RX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [RX_STATE_IDLE_def] THEN
  nic_rw_tactics.rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  nic_rw_tactics.rw_state_tactic `r` [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  COND_CASES_TAC THENL
  [
   REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
   REWRITE_TAC [REWRITE_RULE [DECIDE ``2 < 20 : num``, DECIDE ``0 < 20 : num``] (SPECL [``2 : num``, ``0 : num``] stateTheory.num2rx_abstract_state_11)] THEN
   DECIDE_TAC
   ,
   REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
   REWRITE_TAC [REWRITE_RULE [DECIDE ``3 < 20 : num``, DECIDE ``0 < 20 : num``] (SPECL [``3 : num``, ``0 : num``] stateTheory.num2rx_abstract_state_11)] THEN
   DECIDE_TAC
  ]);

val rw_nic_state_components_and_prove_state_inequality =
  nic_rw_tactics.rw_state_tactic `nic` [stateTheory.nic_state_fn_updates, combinTheory.K_THM, stateTheory.nic_state_accessors] THEN
  nic_rw_tactics.rw_state_tactic `r` [stateTheory.rx_state_fn_updates, combinTheory.K_THM, stateTheory.rx_state_accessors] THEN
  REWRITE_TAC [GSYM stateTheory.num2rx_abstract_state_thm] THEN
  (fn (asl, con) =>
     let val rx_id = (#2 o dest_comb o #1 o dest_eq o dest_neg) con in
      REWRITE_TAC [REWRITE_RULE [DECIDE ``^rx_id < 20 : num``, DECIDE ``0 < 20 : num``] (SPECL [``^rx_id : num``, ``0 : num``] stateTheory.num2rx_abstract_state_11)] (asl, con)
     end) THEN
  DECIDE_TAC;

fun prove_state_inequality_for_current_state_and_transition rx_id =
  let val rx_delta_lemma = rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id
  in
    ASSUME_TAC (UNDISCH (SPEC_ALL rx_delta_lemma)) THEN
    ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``y = rx_transition env nic`` THEN
    PAT_ASSUM ``x = y`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
    REWRITE_TAC rxLib.rx_transition_defs THEN
    REWRITE_TAC [LET_DEF, pairTheory.PAIR_EQ] THEN
    BETA_TAC THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC [RX_STATE_IDLE_def] THEN
    REPEAT (WEAKEN_TAC (fn _ => true)) THEN
    REPEAT (COND_CASES_TAC THENL [rw_nic_state_components_and_prove_state_inequality, ALL_TAC]) THEN
    rw_nic_state_components_and_prove_state_inequality
  end;

val rx_transition_RX_STATE_WRITE_CPPI_RAM_NEXT_STATE_NOT_IDLE_lemma = store_thm (
  "rx_transition_RX_STATE_WRITE_CPPI_RAM_NEXT_STATE_NOT_IDLE_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_WRITE_CPPI_RAM nic
    ==>
    ~RX_STATE_IDLE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC rxLib.RX_STATE_CLASSIFICATION_defs THEN
  REWRITE_TAC [GSYM boolTheory.DISJ_ASSOC] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val disjunct = (#1 o dest_disj o concl) thm in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id disjunct in
      ASM_CASES_TAC disjunct THENL
      [
       prove_state_inequality_for_current_state_and_transition rx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_state_inequality_for_current_state_and_transition 18);

val RX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_CURRENT_STATE_WRITE_CP_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_CURRENT_STATE_WRITE_CP_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_STATE_IDLE nic'
    ==>
    RX_STATE_WRITE_CP nic \/
    ((nic'.tx = nic.tx) /\
     (nic'.rx.state = nic.rx.state) /\ (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\ (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
     (nic'.rd = nic.rd) /\
     (nic'.regs = nic.regs))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_transition_definitionsTheory.RX_AUTONOMOUS_TRANSITION_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_state_lemmasTheory.RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_SPLIT_RX_STATEs_lemma)) THEN
  ASM_CASES_TAC ``RX_STATE_RECEIVE_FRAME nic`` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas 0))) THEN
   ASM_RW_ASM_TAC ``f a0 a1 = (x, y)`` ``(x, y) = f a0 a1`` THEN
   RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_NEXT_STATE_NOT_IDLE_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma)) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC ``~RX_STATE_IDLE nic'`` THENL
   [
    ASM_RW_ASM_TAC ``~RX_STATE_IDLE nic'`` ``RX_STATE_IDLE nic'`` THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~~P`` ``~P \/ Q`` THEN
    ASM_RW_ASM_TAC ``nic' = f a0 a1`` ``P /\ Q`` THEN
    ASM_REWRITE_TAC []
   ]
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  ASM_CASES_TAC ``RX_STATE_FETCH_NEXT_BD nic`` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas 1))) THEN
   ASM_RW_ASM_TAC ``f a0 a1 = (x, y)`` ``(x, y) = f a0 a1`` THEN
   RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_1fetch_next_bd_NEXT_STATE_NOT_IDLE_lemma)) THEN
   ASM_RW_ASM_TAC ``~RX_STATE_IDLE nic'`` ``RX_STATE_IDLE nic'`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  RW_ASM_TAC ``P \/ Q`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def THEN
  RW_ASM_TAC ``P \/ Q`` (GSYM boolTheory.DISJ_ASSOC) THEN
  ASM_CASES_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic`` THENL
  [
   ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas 2))) THEN
   ASM_RW_ASM_TAC ``f a0 a1 = g b2`` ``(x, y) = f a0 a1`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_2issue_next_memory_write_request_NEXT_STATE_NOT_IDLE_lemma)) THEN
   ASM_RW_ASM_TAC ``~RX_STATE_IDLE nic'`` ``RX_STATE_IDLE nic'`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  ASM_CASES_TAC ``RX_STATE_WRITE_CPPI_RAM nic`` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL rx_transition_RX_STATE_WRITE_CPPI_RAM_NEXT_STATE_NOT_IDLE_lemma)) THEN
   ASM_RW_ASM_TAC ``~RX_STATE_IDLE nic'`` ``RX_STATE_IDLE nic'`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_RX_STATE_WRITE_CP_IMP_NEXT_STATE_EQ_rx_19write_cp_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_RX_STATE_WRITE_CP_IMP_NEXT_STATE_EQ_rx_19write_cp_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_STATE_WRITE_CP nic
    ==>
    (nic' = rx_19write_cp env nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [rx_transition_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``x = rx_write_cp`` ``(nic', mr') = x`` THEN
  RW_ASM_TAC ``(nic', mr') = x`` stateTheory.rx_abstract_state_case_def THEN
  RW_ASM_TAC ``(nic', mr') = x`` pairTheory.PAIR_EQ THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_RX_STATE_WRITE_CP_PRESERVES_RX_BD_QUEUE_EMPTY_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_RX_STATE_WRITE_CP_PRESERVES_RX_BD_QUEUE_EMPTY_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_STATE_WRITE_CP nic /\
    RX_BD_QUEUE_EMPTY nic
    ==>
    RX_BD_QUEUE_EMPTY nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_RX_STATE_WRITE_CP_IMP_NEXT_STATE_EQ_rx_19write_cp_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [rx_19write_cp_def] THEN
  nic_rw THEN
  rx_rw THEN
  RW_ASM_TAC ``x = 0w`` stateTheory.nic_state_accessors THEN
  RW_ASM_TAC ``x = 0w`` stateTheory.rx_state_accessors THEN
  ASM_REWRITE_TAC []);

val RX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_NEXT_STATE_EQ_rx_19write_cp_CURRENT_STATE_WRITE_CP_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_NEXT_STATE_EQ_rx_19write_cp_CURRENT_STATE_WRITE_CP_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' /\
    RX_STATE_IDLE nic'
    ==>
    ((nic' = rx_19write_cp env nic) /\ RX_STATE_WRITE_CP nic) \/
    ((nic'.tx = nic.tx) /\
     (nic'.rx.state = nic.rx.state) /\ (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\ (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
     (nic'.rd = nic.rd) /\
     (nic'.regs = nic.regs))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_NEXT_STATE_IDLE_IMP_CURRENT_STATE_WRITE_CP_OR_TX_RX_STATE_RD_CURRENT_BD_PA_REGS_PRESERVED_lemma)) THEN
  ASM_CASES_TAC ``RX_STATE_WRITE_CP nic`` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_AUTONOMOUS_TRANSITION_RX_STATE_WRITE_CP_IMP_NEXT_STATE_EQ_rx_19write_cp_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASM_REWRITE_TAC []
  ]);





val rx_0receive_new_frame_PRESERVES_IT_lemma = store_thm (
  "rx_0receive_new_frame_PRESERVES_IT_lemma",
  ``!nic env nic'.
    (nic' = rx_0receive_new_frame env nic)
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_0receive_new_frame_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  WEAKEN_TAC (fn _ => true) THEN
  REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  COND_CASES_TAC THENL
  [
   nic_rw
   ,
   ALL_TAC
  ] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  COND_CASES_TAC THEN
  nic_rw);

val rx_transition_RX_STATE_RECEIVE_FRAME_PRESERVES_IT_lemma = store_thm (
  "rx_transition_RX_STATE_RECEIVE_FRAME_PRESERVES_IT_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_RECEIVE_FRAME nic
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (List.nth (RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_lemmas, 0)))) THEN
  ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``x = rx_transition env nic`` THEN
  RW_ASM_TAC ``(nic', mr') = (x, y)`` pairTheory.PAIR_EQ THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_0receive_new_frame_PRESERVES_IT_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_1fetch_next_bd_PRESERVES_IT_lemma = store_thm (
  "rx_1fetch_next_bd_PRESERVES_IT_lemma",
  ``!nic nic'.
    (nic' = rx_1fetch_next_bd nic)
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_1fetch_next_bd_def] THEN
  WEAKEN_TAC (fn _ => true) THEN
  COND_CASES_TAC THENL
  [
   nic_rw
   ,
   ALL_TAC
  ] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  COND_CASES_TAC THEN
  nic_rw);

val rx_transition_RX_STATE_FETCH_NEXT_BD_PRESERVES_IT_lemma = store_thm (
  "rx_transition_RX_STATE_FETCH_NEXT_BD_PRESERVES_IT_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_FETCH_NEXT_BD nic
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (List.nth (RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_lemmas, 1)))) THEN
  ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``x = rx_transition env nic`` THEN
  RW_ASM_TAC ``(nic', mr') = (x, y)`` pairTheory.PAIR_EQ THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_1fetch_next_bd_PRESERVES_IT_lemma)) THEN
  ASM_REWRITE_TAC []);

val rx_2issue_next_memory_write_request_PRESERVES_IT_lemma = store_thm (
  "rx_2issue_next_memory_write_request_PRESERVES_IT_lemma",
  ``!nic nic' mr'.
    ((nic', mr') = rx_2issue_next_memory_write_request nic)
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rx_2issue_next_memory_write_request_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC (fn _ => true) THEN
  nic_rw);

val rx_transition_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_PRESERVES_IT_lemma = store_thm (
  "rx_transition_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_PRESERVES_IT_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST nic
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (List.nth (RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_lemmas, 2)))) THEN
  ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``x = rx_transition env nic`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_2issue_next_memory_write_request_PRESERVES_IT_lemma)) THEN
  ASM_REWRITE_TAC []);

fun prove_it_eq_for_current_state_and_transition rx_id =
  let val rx_delta_lemma = rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id
  in
   ASSUME_TAC (UNDISCH (SPEC_ALL (rxLib.get_rx_conjunct RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_CONJ_lemmas rx_id))) THEN
   ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``y = rx_transition env nic`` THEN
   PAT_ASSUM ``x = y`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
   REWRITE_TAC rxLib.rx_transition_defs THEN
   REWRITE_TAC [LET_DEF, pairTheory.PAIR_EQ] THEN
   BETA_TAC THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT (WEAKEN_TAC (fn _ => true)) THEN
   REPEAT (COND_CASES_TAC THENL [nic_rw, ALL_TAC]) THEN
   nic_rw
  end;

val rx_transition_RX_STATE_WRITE_CPPI_RAM_PRESERVES_IT_lemma = store_thm (
  "rx_transition_RX_STATE_WRITE_CPPI_RAM_PRESERVES_IT_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_WRITE_CPPI_RAM nic
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC rxLib.RX_STATE_CLASSIFICATION_defs THEN
  REWRITE_TAC [GSYM boolTheory.DISJ_ASSOC] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val disjunct = (#1 o dest_disj o concl) thm in
    let val rx_id = rxLib.rx_transition_state_application_to_rx_id disjunct in
      ASM_CASES_TAC disjunct THENL
      [
       prove_it_eq_for_current_state_and_transition rx_id
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end)) THEN
  prove_it_eq_for_current_state_and_transition 18);

val rx_19write_cp_PRESERVES_IT_lemma = store_thm (
  "rx_19write_cp_PRESERVES_IT_lemma",
  ``!nic env nic'.
    (nic' = rx_19write_cp env nic)
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [rx_19write_cp_def] THEN
  nic_rw);

val rx_transition_RX_STATE_WRITE_CP_PRESERVES_IT_lemma = store_thm (
  "rx_transition_RX_STATE_WRITE_CP_PRESERVES_IT_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_WRITE_CP nic
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (List.nth (RX_STATE_TRANSITION_IMP_RX_TRANSITION_STEP_EQ_lemmas, 19)))) THEN
  ASM_RW_ASM_TAC ``rx_transition env nic = x`` ``x = rx_transition env nic`` THEN
  RW_ASM_TAC ``(nic', mr') = (x, y)`` pairTheory.PAIR_EQ THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL rx_19write_cp_PRESERVES_IT_lemma)) THEN
  ASM_REWRITE_TAC []);



val rx_transition_state_preserves_it_lemmas = [
  rx_transition_RX_STATE_RECEIVE_FRAME_PRESERVES_IT_lemma,
  rx_transition_RX_STATE_FETCH_NEXT_BD_PRESERVES_IT_lemma,
  rx_transition_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_PRESERVES_IT_lemma,
  rx_transition_RX_STATE_WRITE_CPPI_RAM_PRESERVES_IT_lemma,
  rx_transition_RX_STATE_WRITE_CP_PRESERVES_IT_lemma];

(* Given A, and [a1 /\ b1 ==> c1, ..., an /\ bn ==> cn], returns ai /\ bi ==> ci if bi = A. *)
fun get_lemma term [] =
    raise Fail "rx_transition_lemmasScript.sml:get_lemma: term did not match any lemma."
  | get_lemma term (lemma::lemmas) =
    if compare (term, (#2 o dest_conj o #1 o dest_imp o concl) lemma) = EQUAL then
      CONJ_ANT_TO_HYP lemma
    else
      get_lemma term lemmas;

val RX_AUTONOMOUS_TRANSITION_PRESERVES_IT_lemma = store_thm (
  "RX_AUTONOMOUS_TRANSITION_PRESERVES_IT_lemma",
  ``!nic env nic' mr'.
    RX_AUTONOMOUS_TRANSITION nic env nic' mr'
    ==>
    (nic'.it = nic.it)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_IMP_RX_STATE_FIVE_CASEs_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_AUTONOMOUS_TRANSITION_IMP_RX_TRANSITION_lemma)) THEN
  REPEAT (PAT_ASSUM ``P \/ Q`` (fn thm =>
    let val disjunct = (#1 o dest_disj o concl) thm in
    let val lemmas = map SPEC_ALL rx_transition_state_preserves_it_lemmas in
    let val lemma = get_lemma disjunct lemmas in
      ASM_CASES_TAC disjunct THENL
      [
       ASSUME_TAC lemma THEN
       ASM_REWRITE_TAC []
       ,
       ASSUME_TAC thm THEN
       ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
      ]
    end end end)) THEN
  ASSUME_TAC (get_lemma ``RX_STATE_WRITE_CP nic`` (map SPEC_ALL rx_transition_state_preserves_it_lemmas)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

