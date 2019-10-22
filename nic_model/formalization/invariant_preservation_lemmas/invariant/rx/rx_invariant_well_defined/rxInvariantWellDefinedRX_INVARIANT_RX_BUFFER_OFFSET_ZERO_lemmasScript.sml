open HolKernel Parse boolLib bossLib;
open rxInvariantWellDefinedTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_RX_BUFFER_OFFSET_ZERO_lemmas";

val RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_IMP_RX_BUFFER_OFFSET_REGISTER_EQ_ZERO_lemma = store_thm (
  "RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_IMP_RX_BUFFER_OFFSET_REGISTER_EQ_ZERO_lemma",
  ``!nic.
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic
    ==>
    (nic.regs.RX_BUFFER_OFFSET = 0w)``,
  REWRITE_TAC [RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def]);

val _ = export_theory();

