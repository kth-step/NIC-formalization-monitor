open HolKernel Parse boolLib bossLib;
open stateTheory;
open it_state_definitionsTheory;

val _ = new_theory "it_state_lemmas";

val EQ_INIT_IMP_EQ_INIT_STATE_lemma = store_thm (
  "EQ_INIT_IMP_EQ_INIT_STATE_lemma",
  ``!nic nic'.
    (nic'.it = nic.it)
    ==>
    (nic'.it.state = nic.it.state)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val IT_STATE_INITIALIZED_DEP_lemma = store_thm (
  "IT_STATE_INITIALIZED_DEP_lemma",
  ``!nic nic'.
    (nic'.it.state = nic.it.state) /\
    IT_STATE_INITIALIZED nic
    ==>
    IT_STATE_INITIALIZED nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IT_STATE_INITIALIZED_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

