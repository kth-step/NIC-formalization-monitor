open HolKernel Parse boolLib bossLib;
open rxInvariantWellDefinedTheory;
open rxTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_WELL_DEFINED_lemmas";

val RX_INVARIANT_BD_WELL_DEFINED_IMP_RX_BD_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_lemma = store_thm (
  "RX_INVARIANT_BD_WELL_DEFINED_IMP_RX_BD_WELL_DEFINED_RX_BUFFER_OFFSET_ZERO_lemma",
  ``!bd SOP.
    RX_INVARIANT_BD_WELL_DEFINED bd
    ==>
    RX_BD_WELL_DEFINED bd SOP 0w``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_WELL_DEFINED_def, RX_BD_WELL_DEFINED_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  Cases_on `SOP` THEN
  ASM_REWRITE_TAC [wordsTheory.w2w_0]);

val _ = export_theory();

