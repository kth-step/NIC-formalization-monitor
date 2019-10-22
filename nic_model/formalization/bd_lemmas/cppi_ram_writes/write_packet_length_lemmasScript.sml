open HolKernel Parse boolLib bossLib;
open helperTactics;
open CPPI_RAMTheory;
open bdTheory;
open cppi_ram_writesTheory;

val _ = new_theory "write_packet_length_lemmas";

val write_packet_length_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma = store_thm (
  "write_packet_length_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma",
  ``!packet_length. CPPI_RAM_WRITE_STEP_WRITES_BD (\CPPI_RAM bd_pa. write_packet_length CPPI_RAM bd_pa packet_length)``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [BD_EQ_def] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [write_packet_length_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] (REWRITE_RULE [blastLib.BBLAST_PROVE ``13w : 32 word <=+ 15w``] (SPECL [``bd_pa_w : 32 word``, ``bd_pa_r : 32 word``, ``13w : 32 word``, ``offset : 32 word``] BDs_IN_CPPI_RAM_OFFSETs_IN_BD_NOT_OVERLAPPING_BDs_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))))) THEN
  ASM_REWRITE_TAC [] THEN
  BETA_TAC THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] (REWRITE_RULE [blastLib.BBLAST_PROVE ``12w : 32 word <=+ 15w``] (SPECL [``bd_pa_w : 32 word``, ``bd_pa_r : 32 word``, ``12w : 32 word``, ``offset : 32 word``] BDs_IN_CPPI_RAM_OFFSETs_IN_BD_NOT_OVERLAPPING_BDs_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))))) THEN
  ASM_REWRITE_TAC []);

val write_packet_length_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma = store_thm (
  "write_packet_length_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma",
  ``!packet_length. CPPI_RAM_WRITE_STEP_PRESERVES_NDP (\CPPI_RAM bd_pa. write_packet_length CPPI_RAM bd_pa packet_length)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def] THEN
  BETA_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NDP_UNMODIFIED_def] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [write_packet_length_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL NDP_DISJUNCT_BYTE_13_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL NDP_DISJUNCT_BYTE_12_lemma)) THEN
  ASM_REWRITE_TAC []);

val write_packet_length_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma = store_thm (
  "write_packet_length_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma",
  ``!packet_length. CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP (\CPPI_RAM bd_pa. write_packet_length CPPI_RAM bd_pa packet_length)``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def] THEN
  REWRITE_TAC [write_packet_length_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma, write_packet_length_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma]);

val _ = export_theory();

