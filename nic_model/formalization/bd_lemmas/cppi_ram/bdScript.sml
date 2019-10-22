open HolKernel Parse boolLib bossLib;
open helperTactics;
open CPPI_RAMTheory;
open address_spaceTheory;

val _ = new_theory "bd";

(*
 * Returns the next descriptor pointer of the buffer descriptor at bd_pa.
 *)
val read_ndp_def = Define `read_ndp (bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) =
  read_bd_word bd_pa 0w CPPI_RAM`;


(*
 * True if and only if there is an overlap between the buffer descriptors at
 * physical addresses bd_pa1 and bd_pa2.
 *)
val BDs_OVERLAP_def = Define `BDs_OVERLAP (bd_pa1 : 32 word) (bd_pa2 : 32 word) =
  bd_pa1 <=+ bd_pa2 /\ bd_pa2 <=+ bd_pa1 + 0xFw \/
  bd_pa2 <=+ bd_pa1 /\ bd_pa1 <=+ bd_pa2 + 0xFw`;

val BDs_OVERLAP_SYM_lemma = store_thm (
  "BDs_OVERLAP_SYM_lemma",
  ``!bd_pa1 bd_pa2.
    BDs_OVERLAP bd_pa1 bd_pa2 = BDs_OVERLAP bd_pa2 bd_pa1``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BDs_OVERLAP_def] THEN
  blastLib.BBLAST_PROVE_TAC);


(*********GENERAL LEMMAS FOR pa_to_cppi_ram_offset********)

val NON_OVERLAPPING_BDs_IMP_DISTINCT_BD_PA_OFFSETs_lemma = store_thm (
  "NON_OVERLAPPING_BDs_IMP_DISTINCT_BD_PA_OFFSETs_lemma",
  ``!bd_pa1 offset1 bd_pa2 offset2.
    BD_IN_CPPI_RAM bd_pa1 /\
    BD_IN_CPPI_RAM bd_pa2 /\
    ~BDs_OVERLAP bd_pa1 bd_pa2 /\
    offset1 <=+ 15w /\
    offset2 <=+ 15w
    ==>
    bd_pa1 + offset1 <> bd_pa2 + offset2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_IN_CPPI_RAM_def, CPPI_RAM_START_def, CPPI_RAM_END_def, BDs_OVERLAP_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISTINCT_FROM_LAST_BD_BYTE_lemma = store_thm (
  "NDP_DISTINCT_FROM_LAST_BD_BYTE_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 15w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_15_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_15_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 15w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_14_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_14_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 14w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_13_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_13_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 13w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_12_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_12_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 12w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_11_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_11_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 11w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_10_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_10_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 10w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_9_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_9_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 9w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val NDP_DISJUNCT_BYTE_8_lemma = store_thm (
  "NDP_DISJUNCT_BYTE_8_lemma",
  ``!bd_pa offset.
    offset <=+ 3w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 8w) <> pa_to_cppi_ram_offset (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val BYTE15_DISTINCT_WORD0_2_BYTE0_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "BYTE15_DISTINCT_WORD0_2_BYTE0_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!(bd_pa : 32 word) (word_offset : 32 word).
    word_offset :32 word <=+ 2w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 15w) <>
    pa_to_cppi_ram_offset (bd_pa + word_offset ≪ 2 + 0w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val BYTE15_DISTINCT_WORD0_2_BYTE1_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "BYTE15_DISTINCT_WORD0_2_BYTE1_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!(bd_pa : 32 word) (word_offset : 32 word).
    word_offset :32 word <=+ 2w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 15w) <>
    pa_to_cppi_ram_offset (bd_pa + word_offset ≪ 2 + 1w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val BYTE15_DISTINCT_WORD0_2_BYTE2_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "BYTE15_DISTINCT_WORD0_2_BYTE2_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!(bd_pa : 32 word) (word_offset : 32 word).
    word_offset :32 word <=+ 2w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 15w) <>
    pa_to_cppi_ram_offset (bd_pa + word_offset ≪ 2 + 2w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val BYTE15_DISTINCT_WORD0_2_BYTE3_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "BYTE15_DISTINCT_WORD0_2_BYTE3_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!(bd_pa : 32 word) (word_offset : 32 word).
    word_offset :32 word <=+ 2w
    ==>
    pa_to_cppi_ram_offset (bd_pa + 15w) <>
    pa_to_cppi_ram_offset (bd_pa + word_offset ≪ 2 + 3w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val BITs_10_0_WORD32_EQ_BITs_10_0_WORD16_lemma = store_thm (
  "BITs_10_0_WORD32_EQ_BITs_10_0_WORD16_lemma",
  ``!(b0 : 8 word) (b1 : 8 word) (b2 : 8 word) (b3 : 8 word).
    ((10 -- 0) (concat_word_list [b0; b1; b2; b3]) : 32 word =
     (10 -- 0) (concat_word_list [b0; b1]))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wordsTheory.concat_word_list_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val BITs_15_0_WORD32_EQ_BITs_15_0_WORD16_lemma = store_thm (
  "BITs_15_0_WORD32_EQ_BITs_15_0_WORD16_lemma",
  ``!(b0 : 8 word) (b1 : 8 word) (b2 : 8 word) (b3 : 8 word).
    ((15 -- 0) (concat_word_list [b0; b1; b2; b3]) : 32 word =
     (15 -- 0) (concat_word_list [b0; b1]))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wordsTheory.concat_word_list_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val PA_IN_CPPI_RAM_def = Define `
  PA_IN_CPPI_RAM pa = CPPI_RAM_START <=+ pa /\ pa <+ CPPI_RAM_END`;

val BD_IN_CPPI_RAM_IMP_BD_OFFSET_IN_CPPI_RAM_lemma = store_thm (
  "BD_IN_CPPI_RAM_IMP_BD_OFFSET_IN_CPPI_RAM_lemma",
  ``!bd_pa offset.
    BD_IN_CPPI_RAM bd_pa /\
    offset <=+ 15w
    ==>
    PA_IN_CPPI_RAM (bd_pa + offset)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_IN_CPPI_RAM_def, PA_IN_CPPI_RAM_def, CPPI_RAM_START_def, CPPI_RAM_END_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val DISTINCT_PAs_IN_CPPI_RAM_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "DISTINCT_PAs_IN_CPPI_RAM_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!pa1 pa2.
    pa1 <> pa2 /\
    PA_IN_CPPI_RAM pa1 /\
    PA_IN_CPPI_RAM pa2
    ==>
    pa_to_cppi_ram_offset pa1 <> pa_to_cppi_ram_offset pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PA_IN_CPPI_RAM_def, pa_to_cppi_ram_offset_def, CPPI_RAM_START_def, CPPI_RAM_END_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val DISTINCT_OFFSETS_OF_BD_IN_CPPI_RAM_IMP_DISTINCT_PAs_lemma = store_thm (
  "DISTINCT_OFFSETS_OF_BD_IN_CPPI_RAM_IMP_DISTINCT_PAs_lemma",
  ``!bd_pa offset1 offset2.
    BD_IN_CPPI_RAM bd_pa /\
    offset1 <=+ 15w /\
    offset2 <=+ 15w /\
    offset1 <> offset2
    ==>
    bd_pa + offset1 <> bd_pa + offset2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_IN_CPPI_RAM_def, CPPI_RAM_START_def, CPPI_RAM_END_def] THEN
  blastLib.BBLAST_PROVE_TAC);

val DISTINCT_OFFSETS_OF_BD_IN_CPPI_RAM_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "DISTINCT_OFFSETS_OF_BD_IN_CPPI_RAM_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!bd_pa offset1 offset2.
    BD_IN_CPPI_RAM bd_pa /\
    offset1 <=+ 15w /\
    offset2 <=+ 15w /\
    offset1 <> offset2
    ==>
    pa_to_cppi_ram_offset (bd_pa + offset1) <> pa_to_cppi_ram_offset (bd_pa + offset2)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``offset1 : 32 word``] BD_IN_CPPI_RAM_IMP_BD_OFFSET_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``offset2 : 32 word``] BD_IN_CPPI_RAM_IMP_BD_OFFSET_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (SPEC_ALL DISTINCT_OFFSETS_OF_BD_IN_CPPI_RAM_IMP_DISTINCT_PAs_lemma))) THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (SPECL [``bd_pa + offset1 : 32 word``, ``bd_pa + offset2 : 32 word``] DISTINCT_PAs_IN_CPPI_RAM_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))) THEN
  ASM_REWRITE_TAC []);

val BDs_IN_CPPI_RAM_OFFSETs_IN_BD_NOT_OVERLAPPING_BDs_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma = store_thm (
  "BDs_IN_CPPI_RAM_OFFSETs_IN_BD_NOT_OVERLAPPING_BDs_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma",
  ``!bd_pa1 bd_pa2 offset1 offset2.
    BD_IN_CPPI_RAM bd_pa1 /\
    BD_IN_CPPI_RAM bd_pa2 /\
    ~BDs_OVERLAP bd_pa1 bd_pa2 /\
    offset1 <=+ 15w /\
    offset2 <=+ 15w
    ==>
    pa_to_cppi_ram_offset (bd_pa1 + offset1) <> pa_to_cppi_ram_offset (bd_pa2 + offset2)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON (SPEC_ALL NON_OVERLAPPING_BDs_IMP_DISTINCT_BD_PA_OFFSETs_lemma))))))))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_pa1 : 32 word``, ``offset1 : 32 word``] BD_IN_CPPI_RAM_IMP_BD_OFFSET_IN_CPPI_RAM_lemma)))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_pa2 : 32 word``, ``offset2 : 32 word``] BD_IN_CPPI_RAM_IMP_BD_OFFSET_IN_CPPI_RAM_lemma)))) THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON (SPECL [``bd_pa1 + offset1 : 32 word``, ``bd_pa2 + offset2 : 32 word``] DISTINCT_PAs_IN_CPPI_RAM_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))))))) THEN
  ASM_REWRITE_TAC []);

val NON_OVERLAPPING_BDs_IMP_DISTINCT_BD_PA_OFFSETs_lemma = prove (
  ``!bd_pa1 bd_pa2 offset1 offset2.
    BD_IN_CPPI_RAM bd_pa1 /\
    BD_IN_CPPI_RAM bd_pa2 /\
    ~BDs_OVERLAP bd_pa1 bd_pa2 /\
    offset1 <=+ 15w /\
    offset2 <=+ 15w
    ==>
    bd_pa1 + offset1 <> bd_pa2 + offset2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_IN_CPPI_RAM_def, BDs_OVERLAP_def, CPPI_RAM_START_def, CPPI_RAM_END_def] THEN
  blastLib.BBLAST_PROVE_TAC);


















val BD_EQ_def = Define `
  BD_EQ (bd_pa : 32 word)
        (CPPI_RAM : 13 word -> 8 word)
        (CPPI_RAM' : 13 word -> 8 word) =
  !offset.
  offset <=+ 15w
  ==>
  (CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + offset)) =
   CPPI_RAM' (pa_to_cppi_ram_offset (bd_pa + offset)))`;

val BD_EQ_REFL_lemma = store_thm (
  "BD_EQ_REFL_lemma",
  ``!bd_pa CPPI_RAM. BD_EQ bd_pa CPPI_RAM CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_EQ_def]);

val BD_EQ_IMP_BD_WORDS_EQ_lemma = store_thm (
  "BD_EQ_IMP_BD_WORDS_EQ_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM' offset.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM' /\
    offset <=+ 3w
    ==>
    (read_bd_word bd_pa offset CPPI_RAM = read_bd_word bd_pa offset CPPI_RAM')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_EQ_def, read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : 32 word <=+ 3w ==> offset << 2 + 0w <=+ 15w``)) THEN
  ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : 32 word <=+ 3w ==> offset << 2 + 1w <=+ 15w``)) THEN
  ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : 32 word <=+ 3w ==> offset << 2 + 2w <=+ 15w``)) THEN
  ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : 32 word <=+ 3w ==> offset << 2 + 3w <=+ 15w``)) THEN
  (fn g =>
     let fun t b = ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : 32 word <=+ 3w ==> offset << 2 + ^b <=+ 15w``))
     in
     (t ``0w : 32 word`` THEN t ``1w : 32 word`` THEN t ``2w : 32 word`` THEN t ``3w : 32 word``) g
     end) THEN
  (fn g =>
     let fun t b = PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC thm THEN ASSUME_TAC (REWRITE_RULE [wordsTheory.WORD_ADD_ASSOC] (UNDISCH (SPEC ``offset << 2 + ^b`` thm))))
     in
     (t ``0w : 32 word`` THEN t ``1w : 32 word`` THEN t ``2w : 32 word`` THEN t ``3w : 32 word``) g
     end) THEN
  ASM_REWRITE_TAC []);

val BD_EQ_IMP_EQ_NDP_lemma = store_thm (
  "BD_EQ_IMP_EQ_NDP_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM'
    ==>
    (read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [read_ndp_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (GSYM BD_EQ_IMP_BD_WORDS_EQ_lemma) THEN
  ASM_REWRITE_TAC [] THEN
  blastLib.BBLAST_PROVE_TAC);

val BD_EQ_SYM_lemma = store_thm (
  "BD_EQ_SYM_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM' = BD_EQ bd_pa CPPI_RAM' CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_EQ_def] THEN
  EQ_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (GSYM thm)) THEN
  ASM_REWRITE_TAC []);

val BD_EQ_TRANS_lemma = store_thm (
  "BD_EQ_TRANS_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM' CPPI_RAM''.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM' /\
    BD_EQ bd_pa CPPI_RAM' CPPI_RAM''
    ==>
    BD_EQ bd_pa CPPI_RAM CPPI_RAM''``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_EQ_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``offset : 32 word`` thm)) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``offset : 32 word`` thm)) THEN
  DISCH_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``offset <=+ 15w`` ``P ==> Q``  THEN
  ASM_RW_ASM_TAC ``offset <=+ 15w`` ``P ==> Q``  THEN
  ASM_REWRITE_TAC []);

val BD_EQ_IMP_rx_read_bd_EQ_lemma = store_thm (
  "BD_EQ_IMP_rx_read_bd_EQ_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM'
    ==>
    (rx_read_bd bd_pa CPPI_RAM = rx_read_bd bd_pa CPPI_RAM')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [CPPI_RAMTheory.rx_read_bd_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [CPPI_RAMTheory.bd_data_literal_11] THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``0w <=+ 3w : bd_pa_type``] (SPECL [``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``, ``0w : bd_pa_type``] BD_EQ_IMP_BD_WORDS_EQ_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``1w <=+ 3w : bd_pa_type``] (SPECL [``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``, ``1w : bd_pa_type``] BD_EQ_IMP_BD_WORDS_EQ_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``2w <=+ 3w : bd_pa_type``] (SPECL [``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``, ``2w : bd_pa_type``] BD_EQ_IMP_BD_WORDS_EQ_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``3w <=+ 3w : bd_pa_type``] (SPECL [``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``, ``3w : bd_pa_type``] BD_EQ_IMP_BD_WORDS_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);













val NDP_UNMODIFIED_def = Define `
  NDP_UNMODIFIED (bd_pa : bd_pa_type) (CPPI_RAM : cppi_ram_type) (CPPI_RAM' : cppi_ram_type) =
  !offset.
  offset <=+ 3w
  ==>
  (CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + offset)) =
   CPPI_RAM' (pa_to_cppi_ram_offset (bd_pa + offset)))`;

val BD_EQ_IMP_NDP_UNMODIFIED_lemma = store_thm (
  "BD_EQ_IMP_NDP_UNMODIFIED_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM'
    ==>
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_EQ_def, NDP_UNMODIFIED_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : 32 word <=+ 3w ==> offset <=+ 15w``)) THEN
  PAT_ASSUM ``!x. P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``offset : 32 word`` thm))) THEN
  ASM_REWRITE_TAC []);

val NDP_UNMODIFIED_TRANS_lemma = store_thm (
  "NDP_UNMODIFIED_TRANS_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM' CPPI_RAM''.
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM' /\
    NDP_UNMODIFIED bd_pa CPPI_RAM' CPPI_RAM''
    ==>
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM''``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NDP_UNMODIFIED_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  KEEP_ASM_RW_ASM_TAC ``offset : bd_pa_type <=+ 3w`` ``offset : bd_pa_type <=+ 3w ==> Q`` THEN
  ASM_RW_ASM_TAC ``offset : bd_pa_type <=+ 3w`` ``offset : bd_pa_type <=+ 3w ==> Q`` THEN
  ASM_REWRITE_TAC []);

val BD_EQ_AND_NDP_UNMODIFIED_IMP_NDP_UNMODIFIED_lemma = store_thm (
  "BD_EQ_AND_NDP_UNMODIFIED_IMP_NDP_UNMODIFIED_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM' CPPI_RAM''.
    BD_EQ bd_pa CPPI_RAM' CPPI_RAM'' /\
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM'
    ==>
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM''``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPECL [``bd_pa : bd_pa_type``, ``CPPI_RAM' : cppi_ram_type``, ``CPPI_RAM'' : cppi_ram_type``] BD_EQ_IMP_NDP_UNMODIFIED_lemma)) THEN
  MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
  EXISTS_TAC ``CPPI_RAM' : cppi_ram_type`` THEN
  ASM_REWRITE_TAC []);

val BD_EQ_NDP_UNMODIFIED_TRANS_UNMODIFIED_lemma = store_thm (
  "BD_EQ_NDP_UNMODIFIED_TRANS_UNMODIFIED_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM' CPPI_RAM''.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM' /\
    NDP_UNMODIFIED bd_pa CPPI_RAM' CPPI_RAM''
    ==>
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM''``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_EQ_def, NDP_UNMODIFIED_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x. P`` (fn thm => ASSUME_TAC (SPEC ``offset : bd_pa_type`` thm)) THEN
  PAT_ASSUM ``!x. P`` (fn thm => ASSUME_TAC (SPEC ``offset : bd_pa_type`` thm)) THEN
  ASSUME_TAC (UNDISCH (blastLib.BBLAST_PROVE ``offset : bd_pa_type <=+ 3w ==> offset <=+ 15w``)) THEN
  ASM_RW_ASM_TAC ``offset <=+ 3w `` ``offset <=+ 3w ==> Q`` THEN
  ASM_RW_ASM_TAC ``offset <=+ 15w `` ``offset <=+ 15w ==> Q`` THEN
  ASM_REWRITE_TAC []);

val NDP_UNMODIFIED_IMP_EQ_NDP_lemma = store_thm (
  "NDP_UNMODIFIED_IMP_EQ_NDP_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM'
    ==>
    (read_ndp bd_pa CPPI_RAM = read_ndp bd_pa CPPI_RAM')``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NDP_UNMODIFIED_def] THEN
  DISCH_TAC THEN
  REWRITE_TAC [read_ndp_def] THEN
  REWRITE_TAC [read_bd_word_def] THEN
  REWRITE_TAC [wordsTheory.ZERO_SHIFT, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [wordsTheory.WORD_ADD_0] THEN
  PAT_ASSUM ``P`` (fn thm =>
    let fun gen_thm byte = REWRITE_RULE [blastLib.BBLAST_PROVE ``^byte <=+ 3w``, wordsTheory.WORD_ADD_0] (SPEC byte thm)
    in
    ASSUME_TAC (gen_thm ``0w : 32 word``) THEN
    ASSUME_TAC (gen_thm ``1w : 32 word``) THEN
    ASSUME_TAC (gen_thm ``2w : 32 word``) THEN
    ASSUME_TAC (gen_thm ``3w : 32 word``)
    end) THEN
  ASM_REWRITE_TAC []);








val BD_WRITE_def = Define `
  BD_WRITE (cppi_ram_update : (13 word -> 8 word) -> 32 word -> 13 word -> 8 word) =
  !bd_pa_w bd_pa_r CPPI_RAM.
  BD_IN_CPPI_RAM bd_pa_w /\
  BD_IN_CPPI_RAM bd_pa_r /\
  ~BDs_OVERLAP bd_pa_r bd_pa_w
  ==>
  BD_EQ bd_pa_r CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa_w)`;










val BD_PRESERVED_def = Define `
  BD_PRESERVED (BD_PROPERTY : 32 word -> (13 word -> 8 word) -> bool)
               (bd_pa : 32 word)
               (CPPI_RAM : 13 word -> 8 word)
               (CPPI_RAM' : 13 word -> 8 word) =
  BD_PROPERTY bd_pa CPPI_RAM
  ==>
  BD_PROPERTY bd_pa CPPI_RAM'`;

val BD_PROPERTY_DEPENDS_ONLY_ON_BD_def = Define `
  BD_PROPERTY_DEPENDS_ONLY_ON_BD (BD_PROPERTY : bd_pa_type -> cppi_ram_type -> bool) =
  !bd_pa CPPI_RAM CPPI_RAM'.
  BD_EQ bd_pa CPPI_RAM CPPI_RAM'
  ==>
  (BD_PROPERTY bd_pa CPPI_RAM = BD_PROPERTY bd_pa CPPI_RAM')`;

val BD_WRITE_PRESERVES_BD_PROPERTY_def = Define `
  BD_WRITE_PRESERVES_BD_PROPERTY (cppi_ram_update : (13 word -> 8 word) -> 32 word -> 13 word -> 8 word) BD_PROPERTY =
  !bd_pa CPPI_RAM.
  BD_PRESERVED BD_PROPERTY bd_pa CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa)`;

val BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def = Define `
  BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY cppi_ram_update BD_PROPERTY =
  BD_WRITE_PRESERVES_BD_PROPERTY cppi_ram_update BD_PROPERTY /\
  BD_WRITE cppi_ram_update`;

val BD_AP_PRESERVED_def = Define `
  BD_AP_PRESERVED (BD_AP_PROPERTY : 32 word -> (13 word -> 8 word) -> (32 word -> bool) -> bool)
               (bd_pa : 32 word)
               (CPPI_RAM : 13 word -> 8 word)
               (CPPI_RAM' : 13 word -> 8 word)
               (AP: 32 word -> bool) =
  BD_AP_PROPERTY bd_pa CPPI_RAM AP
  ==>
  BD_AP_PROPERTY bd_pa CPPI_RAM' AP`;

val BD_AP_PROPERTY_DEPENDS_ONLY_ON_BD_AP_def = Define `
  BD_AP_PROPERTY_DEPENDS_ONLY_ON_BD_AP BD_AP_PROPERTY AP =
  !bd_pa CPPI_RAM CPPI_RAM'.
  BD_EQ bd_pa CPPI_RAM CPPI_RAM' ==>
  (BD_AP_PROPERTY bd_pa CPPI_RAM AP = BD_AP_PROPERTY bd_pa CPPI_RAM' AP)`;

val BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_def = Define `
  BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY cppi_ram_update BD_AP_PROPERTY AP =
  !bd_pa CPPI_RAM.
  BD_AP_PRESERVED BD_AP_PROPERTY bd_pa CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa) AP`;

val BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY_def = Define `
  BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY cppi_ram_update BD_AP_PROPERTY AP =
  BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY cppi_ram_update BD_AP_PROPERTY AP /\
  BD_WRITE cppi_ram_update`;














val BD_EQ_AND_NON_OVERLAP_BD_WRITE_IMP_BD_EQ_AFTER_BD_WRITE_lemma = store_thm (
  "BD_EQ_AND_NON_OVERLAP_BD_WRITE_IMP_BD_EQ_AFTER_BD_WRITE_lemma",
  ``!bd_pa_r bd_pa_w CPPI_RAM CPPI_RAM' cppi_ram_update.
    BD_IN_CPPI_RAM bd_pa_r /\
    BD_IN_CPPI_RAM bd_pa_w /\
    BD_EQ bd_pa_r CPPI_RAM CPPI_RAM' /\
    BD_WRITE cppi_ram_update /\
    ~BDs_OVERLAP bd_pa_r bd_pa_w
    ==>
    BD_EQ bd_pa_r CPPI_RAM (cppi_ram_update CPPI_RAM' bd_pa_w)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_w : 32 word``, ``bd_pa_r : 32 word``, ``CPPI_RAM' : 13 word -> 8 word``] thm)) THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_w`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa_r bd_pa_w`` ``P ==> Q`` THEN
  PAT_ASSUM ``BD_EQ bd_pa_r CPPI_RAM CPPI_RAM'`` (fn l =>
    PAT_ASSUM ``BD_EQ bd_pa_r CPPI_RAM' (cppi_ram_update CPPI_RAM' bd_pa_w)`` (fn r =>
    ASSUME_TAC (CONJ l r))) THEN
  MATCH_MP_ASM_IMP_TAC ``P /\ Q`` BD_EQ_TRANS_lemma THEN
  ASM_REWRITE_TAC []);

val BD_EQ_AFTER_BD_WRITE_AND_NON_OVERLAP_BD_WRITE_IMP_BD_EQ_lemma = store_thm (
  "BD_EQ_AFTER_BD_WRITE_AND_NON_OVERLAP_BD_WRITE_IMP_BD_EQ_lemma",
  ``!bd_pa_r bd_pa_w CPPI_RAM CPPI_RAM' cppi_ram_update.
    BD_IN_CPPI_RAM bd_pa_r /\
    BD_IN_CPPI_RAM bd_pa_w /\
    BD_WRITE cppi_ram_update /\
    ~BDs_OVERLAP bd_pa_r bd_pa_w /\
    BD_EQ bd_pa_r CPPI_RAM (cppi_ram_update CPPI_RAM' bd_pa_w)
    ==>
    BD_EQ bd_pa_r CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_w : 32 word``, ``bd_pa_r : 32 word``, ``CPPI_RAM' : 13 word -> 8 word``] thm)) THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_w`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa_r bd_pa_w`` ``P ==> Q`` THEN
  PAT_ASSUM ``BD_EQ bd_pa_r CPPI_RAM' (cppi_ram_update CPPI_RAM' bd_pa_w)`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BD_EQ_SYM_lemma] thm)) THEN
  MATCH_MP_TAC BD_EQ_TRANS_lemma THEN
  EXISTS_TAC ``(cppi_ram_update : (13 word -> 8 word) -> 32 word -> 13 word -> 8 word) CPPI_RAM' bd_pa_w`` THEN
  ASM_REWRITE_TAC []);

val NON_OVERLAPPING_BD_WRITE_PRESERVES_BD_lemma = store_thm (
  "NON_OVERLAPPING_BD_WRITE_PRESERVES_BD_lemma",
  ``!bd_pa_r bd_pa_w CPPI_RAM CPPI_RAM' cppi_ram_update.
    BD_IN_CPPI_RAM bd_pa_r /\
    BD_IN_CPPI_RAM bd_pa_w /\
    BD_WRITE cppi_ram_update /\
    ~BDs_OVERLAP bd_pa_r bd_pa_w
    ==>
    BD_EQ bd_pa_r CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa_w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_WRITE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``BD_IN_CPPI_RAM bd_pa_w`` (fn c1 =>
    PAT_ASSUM ``BD_IN_CPPI_RAM bd_pa_r`` (fn c2 =>
    PAT_ASSUM ``~BDs_OVERLAP bd_pa_r bd_pa_w`` (fn c3 =>
    ASSUME_TAC (LIST_CONJ [c1, c2, c3])))) THEN
  PAT_ASSUM ``P /\ Q`` (fn ant => PAT_ASSUM ``!x.P`` (fn imp => ASSUME_TAC (MATCH_MP imp ant))) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

