open HolKernel Parse boolLib bossLib;
open helperTactics;
open nic_transition_definitionsTheory;
open it_transition_definitionsTheory;
open tx_transition_definitionsTheory;
open rx_transition_definitionsTheory;
open td_transition_definitionsTheory;
open rd_transition_definitionsTheory;
open schedulerTheory;

val _ = new_theory "nic_transition_lemmas";

val NIC_REGISTER_READ_TRANSITION_ID_lemma = store_thm (
  "NIC_REGISTER_READ_TRANSITION_ID_lemma",
  ``!nic env pa nic' value'.
    NIC_REGISTER_READ_TRANSITION nic env pa nic' value'
    ==>
    (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_REGISTER_READ_TRANSITION_def] THEN
  REWRITE_TAC [nic_modelTheory.nic_transition_register_read_def] THEN
  REWRITE_TAC [register_readTheory.read_register_def] THEN
  REPEAT (COND_CASES_TAC THENL
  [
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [pairTheory.PAIR_EQ] THEN
   REWRITE_TAC [GSYM boolTheory.CONJ_ASSOC] THEN
   REWRITE_TAC [boolTheory.AND1_THM]
   ,
   ALL_TAC
  ]) THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  REWRITE_TAC [GSYM boolTheory.CONJ_ASSOC] THEN
  REWRITE_TAC [boolTheory.AND1_THM]);

val SCHEDULER_CASE_INITIALIZE_IMP_IT_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma = store_thm (
  "SCHEDULER_CASE_INITIALIZE_IMP_IT_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case initialize env nic)
    ==>
    IT_AUTONOMOUS_TRANSITION nic nic' \/ (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.scheduler_case_def] THEN
  REWRITE_TAC [IT_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [IT_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val SCHEDULER_CASE_TRANSMIT_IMP_TX_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma = store_thm (
  "SCHEDULER_CASE_TRANSMIT_IMP_TX_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case transmit env nic)
    ==>
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' \/ (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.scheduler_case_def] THEN
  REWRITE_TAC [TX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val SCHEDULER_CASE_RECEIVE_IMP_RX_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma = store_thm (
  "SCHEDULER_CASE_RECEIVE_IMP_RX_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case receive env nic)
    ==>
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' \/ (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.scheduler_case_def] THEN
  REWRITE_TAC [RX_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val SCHEDULER_CASE_TEARDOWN_TRANSMISSION_IMP_TD_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma = store_thm (
  "SCHEDULER_CASE_TEARDOWN_TRANSMISSION_IMP_TD_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case teardown_transmission env nic)
    ==>
    TD_AUTONOMOUS_TRANSITION nic env nic' \/ (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.scheduler_case_def] THEN
  REWRITE_TAC [TD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [TD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val SCHEDULER_CASE_TEARDOWN_RECEPTION_IMP_RD_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma = store_thm (
  "SCHEDULER_CASE_TEARDOWN_RECEPTION_IMP_RD_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case teardown_reception env nic)
    ==>
    RD_AUTONOMOUS_TRANSITION nic env nic' \/ (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [schedulerTheory.scheduler_case_def] THEN
  REWRITE_TAC [RD_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [RD_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val LAMBDA_PAIR_IN_TRIPLE_EQ_lemma = prove (
  ``!nic' l r.
    ((\(nic' : nic_state, mr' : memory_request option). (nic', mr', nic'.interrupt)) (l, r)) =
    (l, r, l.interrupt)``,
  REPEAT GEN_TAC THEN
  (fn (asl, con) =>
   let val lambda = (#1 o dest_eq) con in
   REWRITE_TAC [PairedLambda.PAIRED_BETA_CONV lambda] (asl, con)
   end));

val lemmas = map (UNDISCH o SPEC_ALL) [
  SCHEDULER_CASE_INITIALIZE_IMP_IT_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma,
  SCHEDULER_CASE_TRANSMIT_IMP_TX_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma,
  SCHEDULER_CASE_RECEIVE_IMP_RX_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma,
  SCHEDULER_CASE_TEARDOWN_TRANSMISSION_IMP_TD_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma,
  SCHEDULER_CASE_TEARDOWN_RECEPTION_IMP_RD_AUTONOMOUS_TRANSITION_OR_EQ_NIC_lemma];

fun get_lemma term [] = raise Fail "nic_transition_lemmas: Did not find lemma.\n"
  | get_lemma term (lemma::lemmas) =
    if Term.compare((hd o #1 o dest_thm) lemma, term) = EQUAL then
      lemma
    else
      get_lemma term lemmas;

val NIC_AUTONOMOUS_TRANSITION_CASEs_lemma = store_thm (
  "NIC_AUTONOMOUS_TRANSITION_CASEs_lemma",
  ``!nic env nic' mr' int'.
    NIC_AUTONOMOUS_TRANSITION nic env nic' mr' int'
    ==>
    IT_AUTONOMOUS_TRANSITION nic nic' \/
    TX_AUTONOMOUS_TRANSITION nic env nic' mr' \/
    RX_AUTONOMOUS_TRANSITION nic env nic' mr' \/
    TD_AUTONOMOUS_TRANSITION nic env nic' \/
    RD_AUTONOMOUS_TRANSITION nic env nic' \/
    (nic' = nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [nic_modelTheory.nic_transition_autonomous_def] THEN
  REWRITE_TAC [schedulerTheory.scheduler_def] THEN
  COND_CASES_TAC THENL
  [
   REWRITE_TAC [pairTheory.PAIR_EQ] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  Cases_on `scheduler_case env.scheduler env nic` THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [LAMBDA_PAIR_IN_TRIPLE_EQ_lemma] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  REFLECT_ASM_TAC ``P /\ Q`` THEN
  ASM_RW_ASM_TAC ``P /\ Q`` ``x = y`` THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  Cases_on `env.scheduler` THEN
  (PAT_ASSUM ``(nic', mr') = scheduler_case c env nic`` (fn thm =>
     ASSUME_TAC (get_lemma (concl thm) lemmas)) THEN
   ASM_CASES_TAC ``nic' : nic_state = nic`` THENL
   [
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``nic' <> nic`` ``P \/ Q`` THEN
    ASM_REWRITE_TAC []
   ]));

val NIC_MEMORY_READ_REPLY_TRANSITION_IMP_TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_lemma = store_thm (
  "NIC_MEMORY_READ_REPLY_TRANSITION_IMP_TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_lemma",
  ``!nic mr nic'.
    NIC_MEMORY_READ_REPLY_TRANSITION nic mr nic'
    ==>
    TX_PROCESS_MEMORY_READ_REPLY_TRANSITION nic mr nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_MEMORY_READ_REPLY_TRANSITION_def] THEN
  REWRITE_TAC [nic_modelTheory.nic_transition_memory_read_reply_def] THEN
  REWRITE_TAC [TX_PROCESS_MEMORY_READ_REPLY_TRANSITION_def]);

val scheduler_initialize_IMP_NO_MEMORY_REQUEST_lemma = store_thm (
  "scheduler_initialize_IMP_NO_MEMORY_REQUEST_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case initialize env nic)
    ==>
    (mr' = NONE)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scheduler_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val scheduler_transmit_MEMORY_REQUEST_IMP_tx_transition_memory_read_request_lemma = store_thm (
  "scheduler_transmit_MEMORY_REQUEST_IMP_tx_transition_memory_read_request_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case transmit env nic) /\
    IS_SOME mr'
    ==>
    ((nic', mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    IS_NONE (THE mr').v``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scheduler_case_def] THEN
  REWRITE_TAC [TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [TX_ENABLE_def] THEN
  COND_CASES_TAC THENL
  [
   REWRITE_TAC [txTheory.tx_transition_def] THEN
   Cases_on `nic.tx.state` THEN
   (
    (REWRITE_TAC [stateTheory.tx_abstract_state_case_def] THEN
     REWRITE_TAC [pairTheory.PAIR_EQ] THEN
     DISCH_TAC THEN
     SPLIT_ASM_TAC THEN
     ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
     RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
     UNDISCH_TAC ``F`` THEN
     REWRITE_TAC [])
    ORELSE
    (REWRITE_TAC [stateTheory.tx_abstract_state_case_def] THEN
     REWRITE_TAC [txTheory.tx_2issue_next_memory_read_request_def] THEN
     REWRITE_TAC [LET_DEF] THEN
     BETA_TAC THEN
     REWRITE_TAC [pairTheory.PAIR_EQ] THEN
     DISCH_TAC THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [optionTheory.THE_DEF] THEN
     REWRITE_TAC [stateTheory.memory_request_accfupds] THEN
     REWRITE_TAC [combinTheory.K_THM] THEN
     REWRITE_TAC [optionTheory.IS_NONE_DEF])
   )
   ,
   REWRITE_TAC [pairTheory.PAIR_EQ] THEN
   REPEAT DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
   RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val scheduler_receive_MEMORY_REQUEST_IMP_rx_transition_memory_write_request_lemma = store_thm (
  "scheduler_receive_MEMORY_REQUEST_IMP_rx_transition_memory_write_request_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case receive env nic) /\
    IS_SOME mr'
    ==>
    ((nic', mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    IS_SOME (THE mr').v``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scheduler_case_def] THEN
  REWRITE_TAC [RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_def] THEN
  REWRITE_TAC [RX_ENABLE_def] THEN
  COND_CASES_TAC THENL
  [
   REWRITE_TAC [rxTheory.rx_transition_def] THEN
   Cases_on `nic.rx.state` THEN
   (
    (REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
     REWRITE_TAC [pairTheory.PAIR_EQ] THEN
     DISCH_TAC THEN
     SPLIT_ASM_TAC THEN
     ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
     RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
     UNDISCH_TAC ``F`` THEN
     REWRITE_TAC [])
    ORELSE
    (REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
     REWRITE_TAC [rxTheory.rx_2issue_next_memory_write_request_def] THEN
     REWRITE_TAC [LET_DEF] THEN
     BETA_TAC THEN
     REWRITE_TAC [pairTheory.PAIR_EQ] THEN
     DISCH_TAC THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [optionTheory.THE_DEF] THEN
     REWRITE_TAC [stateTheory.memory_request_accfupds] THEN
     REWRITE_TAC [combinTheory.K_THM] THEN
     REWRITE_TAC [optionTheory.IS_SOME_DEF]
    )
   )
   ,
   REWRITE_TAC [pairTheory.PAIR_EQ] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
   RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val scheduler_teardown_transmission_IMP_NO_MEMORY_REQUEST_lemma = store_thm (
  "scheduler_teardown_transmission_IMP_NO_MEMORY_REQUEST_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case teardown_transmission env nic)
    ==>
    (mr' = NONE)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scheduler_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val scheduler_teardown_reception_IMP_NO_MEMORY_REQUEST_lemma = store_thm (
  "scheduler_teardown_reception_IMP_NO_MEMORY_REQUEST_lemma",
  ``!nic env nic' mr'.
    ((nic', mr') = scheduler_case teardown_reception env nic)
    ==>
    (mr' = NONE)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scheduler_case_def] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val schduler_issues_memory_request_IMP_tx_transition_memory_read_OR_rx_transition_memory_write_lemma = store_thm (
  "schduler_issues_memory_request_IMP_tx_transition_memory_read_OR_rx_transition_memory_write_lemma",
  ``!nic env nic' mr' int'.
    ((nic', mr', int') = scheduler env nic) /\
    IS_SOME mr'
    ==>
    ((nic', mr') = tx_transition env nic) /\ TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\ IS_NONE (THE mr').v \/
    ((nic', mr') = rx_transition env nic) /\ RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\ IS_SOME (THE mr').v``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scheduler_def] THEN
  COND_CASES_TAC THENL
  [
   REWRITE_TAC [pairTheory.PAIR_EQ] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
   RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``~P`` ``x = y`` THEN
  PAT_ASSUM ``x = y`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  Cases_on `scheduler_case env.scheduler env nic` THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  (fn g =>
   let val goal = #2 g in
   let val ant = (#1 o dest_imp) goal in
   let val rhs = (#2 o dest_eq) ant in
     REWRITE_TAC [PairedLambda.PAIRED_BETA_CONV rhs] g
   end end end) THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_TAC THEN
  REFLECT_ASM_TAC ``P /\ Q`` THEN
  ASM_RW_ASM_TAC ``P /\ Q`` ``x = y`` THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  Cases_on `env.scheduler` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL scheduler_initialize_IMP_NO_MEMORY_REQUEST_lemma)) THEN
   ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
   RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL scheduler_transmit_MEMORY_REQUEST_IMP_tx_transition_memory_read_request_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL scheduler_receive_MEMORY_REQUEST_IMP_rx_transition_memory_write_request_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL scheduler_teardown_transmission_IMP_NO_MEMORY_REQUEST_lemma)) THEN
   ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
   RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL scheduler_teardown_reception_IMP_NO_MEMORY_REQUEST_lemma)) THEN
   ASM_RW_ASM_TAC ``mr' = NONE`` ``IS_SOME mr'`` THEN
   RW_ASM_TAC ``IS_SOME NONE`` optionTheory.IS_SOME_DEF THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val NIC_AUTONOMOUS_TRANSITION_MEMORY_REQUEST_IMP_TX_OR_RX_MEMORY_REQUEST_lemma = store_thm (
  "NIC_AUTONOMOUS_TRANSITION_MEMORY_REQUEST_IMP_TX_OR_RX_MEMORY_REQUEST_lemma",
  ``!nic env nic' mr' int'.
    NIC_AUTONOMOUS_TRANSITION nic env nic' mr' int' /\
    IS_SOME mr'
    ==>
    ((nic',mr') = tx_transition env nic) /\
    TX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    IS_NONE (THE mr').v
    \/
    ((nic',mr') = rx_transition env nic) /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    IS_SOME (THE mr').v``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_AUTONOMOUS_TRANSITION_def] THEN
  REWRITE_TAC [nic_modelTheory.nic_transition_autonomous_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC schduler_issues_memory_request_IMP_tx_transition_memory_read_OR_rx_transition_memory_write_lemma THEN
  EXISTS_TAC ``int' : bool`` THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

