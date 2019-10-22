
structure helperTactics :> helperTactics =
struct

  open HolKernel Parse boolLib bossLib;

  fun ASM_RW_ASM_TAC rw_asm asm_rw = PAT_ASSUM rw_asm (fn rw => PAT_ASSUM asm_rw (fn thm => ASSUME_TAC (REWRITE_RULE [rw] thm)));

  fun COPY_ASM_TAC asm_term = PAT_ASSUM asm_term (fn thm => ASSUME_TAC thm THEN ASSUME_TAC thm);

  fun KEEP_ASM_RW_ASM_TAC rw_asm asm_rw = PAT_ASSUM rw_asm (fn rw => PAT_ASSUM asm_rw (fn thm => ASSUME_TAC rw THEN ASSUME_TAC (REWRITE_RULE [rw] thm)));

  fun MATCH_MP_ASM_IMP_TAC asm_term lemma = PAT_ASSUM asm_term (fn ant => ASSUME_TAC (MATCH_MP lemma ant));

  fun MATCH_MP_KEEP_ASM_IMP_TAC asm_term lemma = COPY_ASM_TAC asm_term THEN MATCH_MP_ASM_IMP_TAC asm_term lemma;

  fun REFLECT_ASM_TAC asm_term = PAT_ASSUM asm_term (fn thm => ASSUME_TAC (GSYM thm));

  fun RW_ASM_TAC asm_term rw_thm = PAT_ASSUM asm_term (fn thm => ASSUME_TAC (REWRITE_RULE [rw_thm] thm));

  fun RW_KEEP_ASM_TAC asm_term rw_thm = PAT_ASSUM asm_term (fn thm => ASSUME_TAC thm THEN ASSUME_TAC (REWRITE_RULE [rw_thm] thm));

  val SPLIT_ASM_TAC = REPEAT (PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm) THEN ASSUME_TAC (CONJUNCT2 thm)));

  fun CONJ_ANT_TO_HYP imp_thm =
    let fun conj_tm_to_hyp_conj_thm tm =
      if not (is_conj tm) then
        ASSUME tm
      else
        let val (cl, cr) = dest_conj tm in
        let val hl = conj_tm_to_hyp_conj_thm cl in
        let val hr = conj_tm_to_hyp_conj_thm cr in
        CONJ hl hr end end end in
    let val (ant, suc) = dest_imp (concl imp_thm) in
    let val hyps_ant_thm = conj_tm_to_hyp_conj_thm ant in
    MP imp_thm hyps_ant_thm 
    end end end;

end

