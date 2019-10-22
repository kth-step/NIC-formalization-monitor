open HolKernel Parse boolLib bossLib;
open helperTactics;
open bdTheory;
open CPPI_RAMTheory;
open bd_queue_preservation_lemmasTheory;
open cppi_ram_writesTheory;
open address_spaceTheory;

val _ = new_theory "clear_own_lemmas";

(**Lemmas for transmission automaton only.***)

val BD_WRITE_clear_own_lemma = store_thm (
  "BD_WRITE_clear_own_lemma",
  ``BD_WRITE clear_own``,
  REWRITE_TAC [BD_WRITE_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_EQ_def] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [clear_own_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] (REWRITE_RULE [wordsTheory.WORD_LOWER_EQ_REFL] (SPECL [``bd_pa_w : 32 word``, ``bd_pa_r : 32 word``, ``15w : 32 word``, ``offset : 32 word``] BDs_IN_CPPI_RAM_OFFSETs_IN_BD_NOT_OVERLAPPING_BDs_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))))) THEN
  ASM_REWRITE_TAC []);

val PRESERVES_NDP_clear_own_lemma = prove (
  ``PRESERVES_NDP clear_own``,
  REWRITE_TAC [PRESERVES_NDP_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NDP_UNMODIFIED_def] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [clear_own_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL NDP_DISTINCT_FROM_LAST_BD_BYTE_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_WRITE_PRESERVES_NDP_clear_own_lemma = store_thm (
  "BD_WRITE_PRESERVES_NDP_clear_own_lemma",
  ``BD_WRITE_PRESERVES_NDP clear_own``,
REWRITE_TAC [BD_WRITE_PRESERVES_NDP_def, BD_WRITE_clear_own_lemma, PRESERVES_NDP_clear_own_lemma]);

val BD_QUEUE_PRESERVED_clear_own_lemma = store_thm (
  "BD_QUEUE_PRESERVED_clear_own_lemma",
  ``!q bd_pa start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    MEM bd_pa q /\
    (CPPI_RAM' = clear_own CPPI_RAM bd_pa)
    ==>
    BD_QUEUE q start_bd_pa CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (REWRITE_RULE [BD_WRITE_PRESERVES_NDP_clear_own_lemma] (SPEC ``clear_own`` BD_WRITE_PRESERVES_NDP_OF_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma)))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : 32 word list``, ``start_bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``, ``clear_own CPPI_RAM bd_pa``] BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma)) THEN
ASM_REWRITE_TAC []);

(**Lemmas for transmission automaton only.***)













































(***Lemmas concerning preservation of bd queue*********************************)

val clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma = store_thm (
  "clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma",
  ``CPPI_RAM_WRITE_STEP_WRITES_BD clear_own``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_EQ_def] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [clear_own_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] (REWRITE_RULE [wordsTheory.WORD_LOWER_EQ_REFL] (SPECL [``bd_pa_w : 32 word``, ``bd_pa_r : 32 word``, ``15w : 32 word``, ``offset : 32 word``] BDs_IN_CPPI_RAM_OFFSETs_IN_BD_NOT_OVERLAPPING_BDs_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma)))))))))) THEN
  ASM_REWRITE_TAC []);

val clear_own_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma = store_thm (
  "clear_own_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma",
  ``CPPI_RAM_WRITE_STEP_PRESERVES_NDP clear_own``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NDP_UNMODIFIED_def] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [clear_own_def] THEN
  REWRITE_TAC [LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL NDP_DISTINCT_FROM_LAST_BD_BYTE_lemma)) THEN
  ASM_REWRITE_TAC []);

val clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma = store_thm (
  "clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_lemma",
  ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP clear_own``,
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def] THEN
  REWRITE_TAC [clear_own_CPPI_RAM_WRITE_STEP_WRITES_BD_lemma, clear_own_CPPI_RAM_WRITE_STEP_PRESERVES_NDP_lemma]);












(***********Lemmas concerning preservation of buffer descriptor fields*********)

val CLEAR_OWN_UNMODIFIED_WORDs_0_2_lemma  = store_thm (
  "CLEAR_OWN_UNMODIFIED_WORDs_0_2_lemma",
  ``!bd_pa word_offset CPPI_RAM.
    word_offset <=+ 2w
    ==>
    (read_bd_word bd_pa word_offset (clear_own CPPI_RAM bd_pa) =
     read_bd_word bd_pa word_offset CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [clear_own_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``2w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``word_offset : 32 word``] BYTE15_DISTINCT_WORD0_2_BYTE0_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``2w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``word_offset : 32 word``] BYTE15_DISTINCT_WORD0_2_BYTE1_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``2w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``word_offset : 32 word``] BYTE15_DISTINCT_WORD0_2_BYTE2_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``2w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``word_offset : 32 word``] BYTE15_DISTINCT_WORD0_2_BYTE3_IMP_DISTINCT_CPPI_RAM_OFFSETs_lemma))) THEN
  ASM_REWRITE_TAC []);

val CLEAR_OWN_UNMODIFIED_BYTEs_12_14_lemma  = store_thm (
  "CLEAR_OWN_UNMODIFIED_BYTEs_12_14_lemma",
  ``!bd_pa byte_offset CPPI_RAM.
    byte_offset <=+ 2w
    ==>
    (CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + 12w + byte_offset)) =
     (clear_own CPPI_RAM bd_pa) (pa_to_cppi_ram_offset (bd_pa + 12w + byte_offset)))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [clear_own_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (prove (``byte_offset : 32 word <=+ 2w ==> pa_to_cppi_ram_offset (bd_pa + 15w) <> pa_to_cppi_ram_offset (bd_pa + 12w + byte_offset)``, REWRITE_TAC [pa_to_cppi_ram_offset_def, CPPI_RAM_START_def] THEN blastLib.BBLAST_PROVE_TAC))) THEN
  ASM_REWRITE_TAC []);

val CLEAR_OWN_UNMODIFIED_BITs_0_4_6_7_lemma = store_thm (
  "CLEAR_OWN_UNMODIFIED_BITs_0_4_6_7_lemma",
  ``!bd_pa (bit_offset : num) CPPI_RAM.
    (bit_offset <= 4 \/ (6 <= bit_offset /\ bit_offset <= 7))
    ==>
    ((bit_offset -- bit_offset) (CPPI_RAM (pa_to_cppi_ram_offset (bd_pa + 15w))) =
     (bit_offset -- bit_offset) ((clear_own CPPI_RAM bd_pa) (pa_to_cppi_ram_offset (bd_pa + 15w))))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``P \/ Q`` (DECIDE `` (bit_offset <= 4 \/ 6 <= bit_offset /\ bit_offset <= 7) = ((bit_offset = 0) \/ (bit_offset = 1) \/ (bit_offset = 2) \/ (bit_offset = 3) \/ (bit_offset = 4) \/ (bit_offset = 6) \/ (bit_offset = 7))``) THEN
  (fn g =>
     let val tac = ASM_REWRITE_TAC [clear_own_def, LET_DEF, combinTheory.UPDATE_def] THEN
               BETA_TAC THEN
               blastLib.BBLAST_PROVE_TAC
     in
     let fun t n = Cases_on `bit_offset = ^n` THENL
               [
                tac
                ,
                ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
               ]
     in
     (t ``0 : num`` THEN t ``1 : num`` THEN t ``2 : num`` THEN t ``3 : num`` THEN
      t ``4 : num`` THEN t ``6 : num`` THEN tac) g
     end
     end));

val clear_own_PRESERVES_NDP_lemma = store_thm (
  "clear_own_PRESERVES_NDP_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).ndp = (tx_read_bd bd_pa CPPI_RAM).ndp)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_ndp] THEN
  REWRITE_TAC [REWRITE_RULE [blastLib.BBLAST_PROVE ``0w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``0w : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_WORDs_0_2_lemma)]);

val clear_own_PRESERVES_BP_lemma = store_thm (
  "clear_own_PRESERVES_BP_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).bp = (tx_read_bd bd_pa CPPI_RAM).bp)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_bp] THEN
  REWRITE_TAC [REWRITE_RULE [blastLib.BBLAST_PROVE ``1w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``1w : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_WORDs_0_2_lemma)]);

val clear_own_PRESERVES_BL_lemma = store_thm (
  "clear_own_PRESERVES_BL_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).bl = (tx_read_bd bd_pa CPPI_RAM).bl)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_bl] THEN
  REWRITE_TAC [REWRITE_RULE [blastLib.BBLAST_PROVE ``2w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``2w : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_WORDs_0_2_lemma)]);

val clear_own_PRESERVES_BO_lemma = store_thm (
  "clear_own_PRESERVES_BO_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).bo = (tx_read_bd bd_pa CPPI_RAM).bo)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_bo] THEN
  REWRITE_TAC [REWRITE_RULE [blastLib.BBLAST_PROVE ``2w : 32 word <=+ 2w``] (SPECL [``bd_pa : 32 word``, ``2w : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_WORDs_0_2_lemma)]);

val clear_own_PRESERVES_PL_lemma = store_thm (
  "clear_own_PRESERVES_PL_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).pl = (tx_read_bd bd_pa CPPI_RAM).pl)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_pl] THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [BITs_10_0_WORD32_EQ_BITs_10_0_WORD16_lemma] THEN
  REWRITE_TAC [blastLib.BBLAST_PROVE ``3w : 32 word << 2 = 12w``] THEN
  (fn g =>
     let fun t b = ASSUME_TAC (REWRITE_RULE [blastLib.BBLAST_PROVE ``^b <=+ 2w``] (SPECL [``bd_pa : 32 word``, b, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_BYTEs_12_14_lemma))
     in
     (EVERY (map t [``0w : 32 word``, ``1w : 32 word``])) g
     end) THEN
  ASM_REWRITE_TAC []);

val clear_own_PRESERVES_TD_lemma = store_thm (
  "clear_own_PRESERVES_TD_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).td = (tx_read_bd bd_pa CPPI_RAM).td)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_td] THEN
  ASM_REWRITE_TAC [] THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [prove (``!(b0 : 8 word) (b1 : 8 word) (b2 : 8 word) (b3 : 8 word). (27 -- 27) (concat_word_list [b0; b1; b2; b3]) : 32 word = w2w ((3 -- 3) b3)``, REWRITE_TAC [wordsTheory.concat_word_list_def] THEN blastLib.BBLAST_PROVE_TAC)] THEN
  REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, blastLib.BBLAST_PROVE ``3w : 32 word << 2 + 3w = 15w``] THEN
  REWRITE_TAC [blastLib.BBLAST_PROVE ``!b : 8 word. (w2w ((3 -- 3) b) : 32 word = 1w) = ((3 -- 3) b = 1w)``] THEN
  ASSUME_TAC (REWRITE_RULE [DECIDE ``3 ≤ 4 ∨ 6 ≤ 3 ∧ 3 ≤ 7``] (SPECL [``bd_pa : 32 word``, ``3 : num``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_BITs_0_4_6_7_lemma)) THEN
  ASM_REWRITE_TAC []);

val clear_own_PRESERVES_EOQ_lemma = store_thm (
  "clear_own_PRESERVES_EOQ_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).eoq = (tx_read_bd bd_pa CPPI_RAM).eoq)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_eoq] THEN
  ASM_REWRITE_TAC [] THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [prove (``!(b0 : 8 word) (b1 : 8 word) (b2 : 8 word) (b3 : 8 word). (28 -- 28) (concat_word_list [b0; b1; b2; b3]) : 32 word = w2w ((4 -- 4) b3)``, REWRITE_TAC [wordsTheory.concat_word_list_def] THEN blastLib.BBLAST_PROVE_TAC)] THEN
  REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, blastLib.BBLAST_PROVE ``3w : 32 word << 2 + 3w = 15w``] THEN
  REWRITE_TAC [blastLib.BBLAST_PROVE ``!b : 8 word. (w2w ((4 -- 4) b) : 32 word = 1w) = ((4 -- 4) b = 1w)``] THEN
  ASSUME_TAC (REWRITE_RULE [DECIDE ``4 ≤ 4 ∨ 6 ≤ 4 ∧ 4 ≤ 7``] (SPECL [``bd_pa : 32 word``, ``4 : num``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_BITs_0_4_6_7_lemma)) THEN
  ASM_REWRITE_TAC []);

val clear_own_PRESERVES_EOP_lemma = store_thm (
  "clear_own_PRESERVES_EOP_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).eop = (tx_read_bd bd_pa CPPI_RAM).eop)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_eop] THEN
  ASM_REWRITE_TAC [] THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [prove (``!(b0 : 8 word) (b1 : 8 word) (b2 : 8 word) (b3 : 8 word). (30 -- 30) (concat_word_list [b0; b1; b2; b3]) : 32 word = w2w ((6 -- 6) b3)``, REWRITE_TAC [wordsTheory.concat_word_list_def] THEN blastLib.BBLAST_PROVE_TAC)] THEN
  REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, blastLib.BBLAST_PROVE ``3w : 32 word << 2 + 3w = 15w``] THEN
  REWRITE_TAC [blastLib.BBLAST_PROVE ``!b : 8 word. (w2w ((6 -- 6) b) : 32 word = 1w) = ((6 -- 6) b = 1w)``] THEN
  ASSUME_TAC (REWRITE_RULE [DECIDE ``6 ≤ 4 ∨ 6 ≤ 6 ∧ 6 ≤ 7``] (SPECL [``bd_pa : 32 word``, ``6 : num``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_BITs_0_4_6_7_lemma)) THEN
  ASM_REWRITE_TAC []);

val clear_own_PRESERVES_SOP_lemma = store_thm (
  "clear_own_PRESERVES_SOP_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    ((tx_read_bd bd_pa (clear_own CPPI_RAM bd_pa)).sop = (tx_read_bd bd_pa CPPI_RAM).sop)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_sop] THEN
  ASM_REWRITE_TAC [] THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [read_bd_word_def, LET_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC [prove (``!(b0 : 8 word) (b1 : 8 word) (b2 : 8 word) (b3 : 8 word). (31 -- 31) (concat_word_list [b0; b1; b2; b3]) : 32 word = w2w ((7 -- 7) b3)``, REWRITE_TAC [wordsTheory.concat_word_list_def] THEN blastLib.BBLAST_PROVE_TAC)] THEN
  REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, blastLib.BBLAST_PROVE ``3w : 32 word << 2 + 3w = 15w``] THEN
  REWRITE_TAC [blastLib.BBLAST_PROVE ``!b : 8 word. (w2w ((7 -- 7) b) : 32 word = 1w) = ((7 -- 7) b = 1w)``] THEN
  ASSUME_TAC (REWRITE_RULE [DECIDE ``7 ≤ 4 ∨ 6 ≤ 7 ∧ 7 ≤ 7``] (SPECL [``bd_pa : 32 word``, ``7 : num``, ``CPPI_RAM : 13 word -> 8 word``] CLEAR_OWN_UNMODIFIED_BITs_0_4_6_7_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

