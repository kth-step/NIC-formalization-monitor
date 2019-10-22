signature helperTactics =
sig

  (*
   * Uses the first term to rewrite the second term, both in the assumption
   * list.
   *)
  val ASM_RW_ASM_TAC : Term.term -> Term.term -> Abbrev.tactic;

  (*
   * The given term in the assumption list is copied.
   *)
  val COPY_ASM_TAC : Term.term -> Abbrev.tactic;

  (*
   * Uses the first term to rewrite the second term, both in the assumption
   * list. The first term is not removed from the assumption list.
   *)
  val KEEP_ASM_RW_ASM_TAC : Term.term -> Term.term -> Abbrev.tactic;

  (*
   * The supplied term, occuring in the assumption list, is the antecedent in
   * and the supplied lemma is (potentially universally quantified)
   * implication. The antecedent is matched with lemma in an application of
   * modus ponens to add the matching succedent of the lemma to the assumption
   * list. The supplied term is removed from the assumption list.
   *)
  val MATCH_MP_ASM_IMP_TAC : Term.term -> Thm.thm -> Abbrev.tactic;

  (*
   * The supplied term, occuring in the assumption list, is the antecedent in
   * and the supplied lemma is (potentially universally quantified)
   * implication. The antecedent is matched with lemma in an application of
   * modus ponens to add the matching succedent of the lemma to the assumption
   * list. The supplied term is not removed from the assumption list.
   *)
  val MATCH_MP_KEEP_ASM_IMP_TAC : Term.term -> Thm.thm -> Abbrev.tactic;

  (*
   * The assumption x = y is rewritten to y = x.
   *)
  val REFLECT_ASM_TAC : Term.term -> Abbrev.tactic;

  (*
   * Rewrites the term in the assumption list with the theorem.
   *)
  val RW_ASM_TAC : Term.term -> Thm.thm -> Abbrev.tactic;

  (*
   * Rewrites the term in the assumption list with the theorem. The rewritten
   * assumption is not removed from the assumption list.
   *)
  val RW_KEEP_ASM_TAC : Term.term -> Thm.thm -> Abbrev.tactic;

  (*
   * All conjunctions in the assumption list are split into individual terms in
   * the assumption list.
   *)
  val SPLIT_ASM_TAC : Abbrev.tactic;

  (*
   * Given a theorem of the form A /\ B /\ C ==> D, returns a theorem of the
   * form A, B, C |- D. The nesting of conjuncts in the antecedent does not
   * matter.
   *)
  val CONJ_ANT_TO_HYP : Thm.thm -> Thm.thm;

end

