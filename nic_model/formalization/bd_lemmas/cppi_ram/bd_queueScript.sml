open HolKernel Parse boolLib bossLib;
open helperTactics;
open bdTheory;
open bd_listTheory;

val _ = new_theory "bd_queue";

(*
 * True if and only if:
 * -Base case: Queue is empty and start address is zero.
 * -Inductive case: Head is start address, not zero, and points to head of tail, which is a
 *  BD_QUEUE.
 *)
val BD_QUEUE_def = Define `
  (BD_QUEUE ([] : 32 word list) (start_bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) = (start_bd_pa = 0w)) /\
  (BD_QUEUE (h::t : 32 word list) (start_bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) =
   (h = start_bd_pa) /\ h <> 0w /\ BD_QUEUE t (read_ndp h CPPI_RAM) CPPI_RAM)`;

val BD_QUEUE_EMPTY_START_ZERO_lemma = store_thm (
  "BD_QUEUE_EMPTY_START_ZERO_lemma",
  ``!CPPI_RAM. BD_QUEUE [] 0w CPPI_RAM``,
  GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_def]);

val BD_QUEUE_IMP_HEAD_EQ_START_lemma = store_thm (
  "BD_QUEUE_IMP_HEAD_EQ_START_lemma",
  ``!h h' t CPPI_RAM.
    BD_QUEUE (h::t) h' CPPI_RAM
    ==>
    (h = h')``,
  REPEAT GEN_TAC THEN
  Cases_on `t` THEN
  REWRITE_TAC [BD_QUEUE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_HEAD_NOT_ZERO_lemma = store_thm (
  "BD_QUEUE_HEAD_NOT_ZERO_lemma",
  ``!h t CPPI_RAM.
    BD_QUEUE (h::t) h CPPI_RAM
    ==>
    h <> 0w``,
  REPEAT GEN_TAC THEN
  Cases_on `t` THEN
  REWRITE_TAC [BD_QUEUE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_START_NOT_ZERO_IMP_NOT_QUEUE_EMPTY_lemma = store_thm (
  "BD_QUEUE_START_NOT_ZERO_IMP_NOT_QUEUE_EMPTY_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    q <> []``,
  REPEAT GEN_TAC THEN
  Cases_on `q` THENL
  [
   REWRITE_TAC [BD_QUEUE_def, boolTheory.NOT_AND]
   ,
   REWRITE_TAC [listTheory.NOT_CONS_NIL]
  ]);

val BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma = store_thm (
  "BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    ?t. q = start_bd_pa::t``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``q : 32 word list``, ``start_bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_START_NOT_ZERO_IMP_NOT_QUEUE_EMPTY_lemma)))))) THEN
  Cases_on `q` THENL
  [
   RW_ASM_TAC ``[] <> []`` boolTheory.REFL_CLAUSE THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   EXISTS_TAC ``t : 32 word list`` THEN
   REWRITE_TAC [listTheory.CONS_11] THEN
   ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa : 32 word``, ``t : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val BD_QUEUE_START_BD_PA_NEQ_ZERO_IMP_MEM_START_BD_PA_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_START_BD_PA_NEQ_ZERO_IMP_MEM_START_BD_PA_BD_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    MEM start_bd_pa q``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val BD_QUEUE_IMP_TL_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_IMP_TL_BD_QUEUE_lemma",
  ``!h t CPPI_RAM.
    BD_QUEUE (h::t) h CPPI_RAM
    ==>
    BD_QUEUE t (read_ndp h CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  Cases_on `t` THEN
  REWRITE_TAC [BD_QUEUE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_EMPTY_IMP_START_EQ_ZERO_lemma = store_thm (
  "BD_QUEUE_EMPTY_IMP_START_EQ_ZERO_lemma",
  ``!start_bd_pa CPPI_RAM.
    BD_QUEUE [] start_bd_pa CPPI_RAM
    ==>
    (start_bd_pa = 0w)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_def]);

val EQ_START_EQ_QUEUEs_lemma = store_thm (
  "EQ_START_EQ_QUEUEs_lemma",
  ``!q1 q2 start_bd_pa CPPI_RAM.
    BD_QUEUE q1 start_bd_pa CPPI_RAM /\
    BD_QUEUE q2 start_bd_pa CPPI_RAM
    ==>
    (q1 = q2)``,
  Induct_on `q1` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [BD_QUEUE_def] THEN
   Cases_on `q2` THENL
   [
    REWRITE_TAC []
    ,
    REWRITE_TAC [BD_QUEUE_def] THEN
    DISCH_TAC THEN
    SPLIT_ASM_TAC THEN
    ASM_RW_ASM_TAC ``start_bd_pa = 0w`` ``h = start_bd_pa`` THEN
    ASM_RW_ASM_TAC ``h = 0w`` ``h ≠ 0w`` THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
   ]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   Cases_on `q2` THENL
   [
    MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE [] start_bd_pa CPPI_RAM`` BD_QUEUE_EMPTY_IMP_START_EQ_ZERO_lemma THEN
    RW_ASM_TAC ``BD_QUEUE (h::q1) start_bd_pa CPPI_RAM`` BD_QUEUE_def THEN
    SPLIT_ASM_TAC THEN
    ASM_RW_ASM_TAC ``start_bd_pa = 0w`` ``h = start_bd_pa`` THEN
    ASM_RW_ASM_TAC ``h = 0w`` ``h ≠ 0w`` THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
    ,
    MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE (h::q1) start_bd_pa CPPI_RAM`` BD_QUEUE_IMP_HEAD_EQ_START_lemma THEN
    MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE (h'::t) start_bd_pa CPPI_RAM`` BD_QUEUE_IMP_HEAD_EQ_START_lemma THEN
    ASM_REWRITE_TAC [listTheory.CONS_11] THEN
    REFLECT_ASM_TAC ``h = start_bd_pa`` THEN
    KEEP_ASM_RW_ASM_TAC ``start_bd_pa = h`` ``BD_QUEUE (h::q1) start_bd_pa CPPI_RAM`` THEN
    REFLECT_ASM_TAC ``h' = start_bd_pa`` THEN
    KEEP_ASM_RW_ASM_TAC ``start_bd_pa = h'`` ``BD_QUEUE (h'::t) start_bd_pa CPPI_RAM`` THEN
    ASM_RW_ASM_TAC ``start_bd_pa = h'`` ``start_bd_pa = h`` THEN
    ASM_RW_ASM_TAC ``h' = h`` ``BD_QUEUE (h'::t) h' CPPI_RAM`` THEN
    MATCH_MP_ASM_IMP_TAC ``BD_QUEUE (h::q1) h CPPI_RAM`` BD_QUEUE_IMP_TL_BD_QUEUE_lemma THEN
    MATCH_MP_ASM_IMP_TAC ``BD_QUEUE (h::t) h CPPI_RAM`` BD_QUEUE_IMP_TL_BD_QUEUE_lemma THEN
    PAT_ASSUM ``BD_QUEUE q1 (read_ndp h CPPI_RAM) CPPI_RAM`` (fn l => PAT_ASSUM ``BD_QUEUE t (read_ndp h CPPI_RAM) CPPI_RAM`` (fn r => ASSUME_TAC (CONJ l r))) THEN
    PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val BD_QUEUE_EXTENSION_lemma = store_thm (
  "BD_QUEUE_EXTENSION_lemma",
  ``!h t CPPI_RAM.
    BD_QUEUE t (read_ndp h CPPI_RAM) CPPI_RAM /\
    h <> 0w /\
    (read_ndp h CPPI_RAM = h)
    ==>
    BD_QUEUE (h::t) (read_ndp h CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

(*
 * Lemma stating that the head of a buffer descriptor queue cannot point to
 * itself.
 *)
val BD_QUEUE_HEAD_NOT_EQ_NDP_lemma = store_thm (
  "BD_QUEUE_HEAD_NOT_EQ_NDP_lemma",
  ``!h t start_bd_pa CPPI_RAM.
    BD_QUEUE (h::t) start_bd_pa CPPI_RAM
    ==>
    start_bd_pa <> (read_ndp start_bd_pa CPPI_RAM)``,
  Induct_on `t` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [BD_QUEUE_def] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   KEEP_ASM_RW_ASM_TAC ``h = start_bd_pa`` ``h ≠ 0w`` THEN
   KEEP_ASM_RW_ASM_TAC ``h = start_bd_pa`` ``read_ndp h CPPI_RAM = 0w`` THEN
   ASM_REWRITE_TAC []
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE l a m`` BD_QUEUE_IMP_HEAD_EQ_START_lemma THEN
   REFLECT_ASM_TAC ``h' = start_bd_pa`` THEN
   ASM_REWRITE_TAC [] THEN
   ASM_RW_ASM_TAC ``start_bd_pa = h'`` ``BD_QUEUE l a m`` THEN
   RW_ASM_TAC ``BD_QUEUE l a m`` BD_QUEUE_def THEN
   SPLIT_ASM_TAC THEN
   CCONTR_TAC THEN
   PAT_ASSUM ``~~P`` (fn thm => ASSUME_TAC (REWRITE_RULE [] thm)) THEN
   REFLECT_ASM_TAC ``h' = read_ndp h' CPPI_RAM`` THEN
   KEEP_ASM_RW_ASM_TAC ``read_ndp h' CPPI_RAM = h'`` ``h = read_ndp h' CPPI_RAM`` THEN
   REFLECT_ASM_TAC ``h = h'`` THEN
   ASM_RW_ASM_TAC ``h' = h`` ``read_ndp h' CPPI_RAM = h'`` THEN
   ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL BD_QUEUE_EXTENSION_lemma)))) THEN
   PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``BD_QUEUE (h::t) a m`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
   ASM_RW_ASM_TAC ``read_ndp h CPPI_RAM = h`` ``l ≠ r`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

val BD_QUEUE_IMP_ALL_TAILS_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_IMP_ALL_TAILS_BD_QUEUE_lemma",
  ``!q q1 q2 start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    (q = q1 ++ q2)
    ==>
    ?h2. BD_QUEUE q2 h2 CPPI_RAM``,
  Induct_on `q` THENL
  [
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``[] = q1 ++ q2`` listTheory.APPEND_eq_NIL THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC ``0w : 32 word`` THEN
   REWRITE_TAC [BD_QUEUE_def]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   Cases_on `q1` THENL
   [
    RW_ASM_TAC ``h::q = [] ++ q2`` listTheory.APPEND THEN
    ASM_RW_ASM_TAC ``h::q = q2`` ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` THEN
    EXISTS_TAC ``start_bd_pa : 32 word`` THEN
    ASM_REWRITE_TAC []
    ,
    PAT_ASSUM ``h::q = h'::t ++ q2`` (fn thm => ASSUME_TAC (CONJUNCT2 (REWRITE_RULE [listTheory.APPEND, listTheory.CONS_11] thm))) THEN
    RW_ASM_TAC ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` BD_QUEUE_def THEN
    SPLIT_ASM_TAC THEN
    PAT_ASSUM ``BD_QUEUE q a m`` (fn l => PAT_ASSUM ``q = t ++ q2`` (fn r => ASSUME_TAC (CONJ l r))) THEN
    PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val NON_LAST_IN_Q_THEN_NEXT_IN_Q_lemma = store_thm (
  "NON_LAST_IN_Q_THEN_NEXT_IN_Q_lemma",
  ``!q start_bd_pa CPPI_RAM bd_pa h.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    (read_ndp bd_pa CPPI_RAM <> 0w) /\
    (read_ndp bd_pa CPPI_RAM = h) /\
    MEM bd_pa q
    ==>
    MEM h q``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``MEM bd_pa q`` listTheory.MEM_SPLIT THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  ASM_REWRITE_TAC [listTheory.MEM_APPEND] THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  ASM_RW_ASM_TAC ``q = l1 ++ bd_pa::l2`` ``BD_QUEUE q start_bd_pa CPPI_RAM`` THEN
  PAT_ASSUM ``BD_QUEUE (l1 ++ bd_pa::l2) start_bd_pa CPPI_RAM`` (fn ant => ASSUME_TAC (MP (REWRITE_RULE [] (SPECL [``l1 ++ bd_pa::l2 : 32 word list``, ``l1 : 32 word list``, ``bd_pa::l2 : 32 word list``, ``start_bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_ALL_TAILS_BD_QUEUE_lemma)) ant)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE l a m`` BD_QUEUE_IMP_HEAD_EQ_START_lemma THEN
  REFLECT_ASM_TAC ``bd_pa = h2`` THEN
  ASM_RW_ASM_TAC ``h2 = bd_pa`` ``BD_QUEUE l a m`` THEN
  Cases_on `l2` THENL
  [
   RW_ASM_TAC ``BD_QUEUE l a m`` BD_QUEUE_def THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``read_ndp bd_pa CPPI_RAM = 0w`` ``read_ndp bd_pa CPPI_RAM ≠ 0w`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  RW_ASM_TAC ``BD_QUEUE l a m`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``read_ndp bd_pa CPPI_RAM = h`` ``h' = read_ndp bd_pa CPPI_RAM`` THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val HEAD_IN_BD_QUEUE_NO_BD_QUEUE_lemma = store_thm (
  "HEAD_IN_BD_QUEUE_NO_BD_QUEUE_lemma",
  ``!bd_pa q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q
    ==>
    ~BD_QUEUE (bd_pa::q) bd_pa CPPI_RAM``,
  Induct_on `q` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.MEM]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   Cases_on `h <> read_ndp bd_pa CPPI_RAM` THENL
   [
    ASM_REWRITE_TAC [BD_QUEUE_def]
    ,
    ALL_TAC
   ] THEN
   PAT_ASSUM ``~~P`` (fn thm => ASSUME_TAC (REWRITE_RULE [] thm)) THEN
   Cases_on `bd_pa = h` THENL
   [
    ASM_RW_ASM_TAC ``bd_pa = h`` ``h = read_ndp bd_pa CPPI_RAM`` THEN
    MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` BD_QUEUE_IMP_HEAD_EQ_START_lemma THEN
    REFLECT_ASM_TAC ``h = start_bd_pa`` THEN
    ASM_RW_ASM_TAC ``start_bd_pa = h`` ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` THEN
    MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE (h::q) h CPPI_RAM`` BD_QUEUE_HEAD_NOT_EQ_NDP_lemma THEN
    REFLECT_ASM_TAC ``h = read_ndp h CPPI_RAM`` THEN
    ASM_RW_ASM_TAC ``read_ndp h CPPI_RAM = h`` ``h ≠ read_ndp h CPPI_RAM`` THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
    ,
    ALL_TAC
   ] THEN
   RW_ASM_TAC ``MEM bd_pa (h::q)`` listTheory.MEM THEN
   ASM_RW_ASM_TAC ``bd_pa ≠ h`` ``P \/ Q`` THEN
   RW_ASM_TAC ``BD_QUEUE l a m`` BD_QUEUE_def THEN
   SPLIT_ASM_TAC THEN
   Cases_on `q` THENL
   [
    RW_ASM_TAC ``MEM bd_pa []`` listTheory.MEM THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
    ,
    ALL_TAC
   ] THEN
   MATCH_MP_KEEP_ASM_IMP_TAC ``BD_QUEUE (h'::t) (read_ndp h CPPI_RAM) CPPI_RAM`` BD_QUEUE_IMP_HEAD_EQ_START_lemma THEN
   KEEP_ASM_RW_ASM_TAC ``h = read_ndp bd_pa CPPI_RAM`` ``BD_QUEUE (h''::t) (read_ndp h CPPI_RAM) CPPI_RAM`` THEN
   KEEP_ASM_RW_ASM_TAC ``h = read_ndp bd_pa CPPI_RAM`` ``h ≠ 0w`` THEN
   PAT_ASSUM ``BD_QUEUE (h'::t) (read_ndp h CPPI_RAM) CPPI_RAM`` (fn thm1 => PAT_ASSUM ``read_ndp bd_pa CPPI_RAM ≠ 0w`` (fn thm2 => PAT_ASSUM ``h = read_ndp bd_pa CPPI_RAM`` (fn thm3 => PAT_ASSUM ``MEM bd_pa (h''::t)`` (fn thm4 => ASSUME_TAC thm3 THEN ASSUME_TAC (CONJ thm1 (CONJ thm2 (CONJ (SYM thm3) thm4))))))) THEN
   MATCH_MP_KEEP_ASM_IMP_TAC ``P /\ Q`` NON_LAST_IN_Q_THEN_NEXT_IN_Q_lemma THEN
   PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm)) THEN
   REFLECT_ASM_TAC ``h' = read_ndp h CPPI_RAM`` THEN
   REFLECT_ASM_TAC ``h = read_ndp bd_pa CPPI_RAM`` THEN

   KEEP_ASM_RW_ASM_TAC ``read_ndp bd_pa CPPI_RAM = h`` ``BD_QUEUE (h'::t) (read_ndp (read_ndp bd_pa CPPI_RAM) CPPI_RAM) CPPI_RAM`` THEN
   ASM_RW_ASM_TAC ``read_ndp h CPPI_RAM = h'`` ``BD_QUEUE (h'::t) start CPPI_RAM`` THEN
   PAT_ASSUM ``BD_QUEUE (h'::t) h' CPPI_RAM`` (fn thm1 => PAT_ASSUM ``MEM h (h''::t)`` (fn thm2 => ASSUME_TAC (CONJ thm1 thm2))) THEN
   PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
   ONCE_REWRITE_TAC [BD_QUEUE_def] THEN
   REFLECT_ASM_TAC ``read_ndp bd_pa CPPI_RAM = h`` THEN
   ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
   ASM_RW_ASM_TAC ``h = read_ndp bd_pa CPPI_RAM`` ``¬BD_QUEUE (h::h'::t) h CPPI_RAM`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_QUEUE_ALL_DISTINCT_lemma = store_thm (
  "BD_QUEUE_ALL_DISTINCT_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM
    ==>
    ALL_DISTINCT q``,
  Induct_on `q` THENL
  [
   REWRITE_TAC [listTheory.ALL_DISTINCT]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   RW_KEEP_ASM_TAC ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` BD_QUEUE_def THEN
   SPLIT_ASM_TAC THEN
   PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``BD_QUEUE q a m`` (fn ant => ASSUME_TAC (MATCH_MP imp ant) THEN ASSUME_TAC ant)) THEN
   REWRITE_TAC [listTheory.ALL_DISTINCT] THEN
   ASM_REWRITE_TAC [] THEN
   WEAKEN_TAC (fn term => equal (#1 (dest_comb term)) ``ALL_DISTINCT : 32 word list -> bool``) THEN
   CCONTR_TAC THEN
   PAT_ASSUM ``~~P`` (fn thm => ASSUME_TAC (REWRITE_RULE [] thm)) THEN
   PAT_ASSUM ``BD_QUEUE q (read_ndp h CPPI_RAM) CPPI_RAM`` (fn thm1 => PAT_ASSUM ``MEM h q`` (fn thm2 => ASSUME_TAC (CONJ thm1 thm2))) THEN
   MATCH_MP_ASM_IMP_TAC ``P /\ Q`` HEAD_IN_BD_QUEUE_NO_BD_QUEUE_lemma THEN
   ASM_RW_ASM_TAC ``h = start_bd_pa`` ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` THEN
   ASM_RW_ASM_TAC ``BD_QUEUE (h::q) h CPPI_RAM`` ``¬BD_QUEUE (h::q) h CPPI_RAM`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
  ]);

















val BD_QUEUE_IMP_EQ_START_BD_PA_lemma = store_thm (
  "BD_QUEUE_IMP_EQ_START_BD_PA_lemma",
  ``!q start_bd_pa start_bd_pa' CPPI_RAM CPPI_RAM'.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa' CPPI_RAM'
    ==>
    (start_bd_pa = start_bd_pa')``,
  REPEAT GEN_TAC THEN
  Cases_on `q` THENL
  [
   REWRITE_TAC [BD_QUEUE_def] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa : 32 word``, ``t : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
   ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa' : 32 word``, ``t : 32 word list``, ``CPPI_RAM' : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
   REFLECT_ASM_TAC ``h = start_bd_pa`` THEN
   REFLECT_ASM_TAC ``h = start_bd_pa'`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_QUEUE_NON_EMPTY_IMP_EQ_NDP_lemma = store_thm (
  "BD_QUEUE_NON_EMPTY_IMP_EQ_NDP_lemma",
  ``!h t start_bd_pa start_bd_pa' CPPI_RAM CPPI_RAM'.
    BD_QUEUE (h::t) start_bd_pa CPPI_RAM /\
    BD_QUEUE (h::t) start_bd_pa' CPPI_RAM'
    ==>
    (read_ndp start_bd_pa CPPI_RAM = read_ndp start_bd_pa' CPPI_RAM')``,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa : 32 word``, ``t : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
   ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa' : 32 word``, ``t : 32 word list``, ``CPPI_RAM' : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
   REFLECT_ASM_TAC ``h = start_bd_pa`` THEN
   REFLECT_ASM_TAC ``h = start_bd_pa'`` THEN
   ASM_REWRITE_TAC [] THEN
   ASM_RW_ASM_TAC ``start_bd_pa = h`` ``BD_QUEUE (h::t) start_bd_pa CPPI_RAM`` THEN
   ASM_RW_ASM_TAC ``start_bd_pa' = h`` ``BD_QUEUE (h::t) start_bd_pa' CPPI_RAM'`` THEN
   MATCH_MP_ASM_IMP_TAC ``BD_QUEUE (h::t) h CPPI_RAM`` BD_QUEUE_IMP_TL_BD_QUEUE_lemma THEN
   MATCH_MP_ASM_IMP_TAC ``BD_QUEUE (h::t) h CPPI_RAM'`` BD_QUEUE_IMP_TL_BD_QUEUE_lemma THEN
   PAT_ASSUM ``BD_QUEUE t (read_ndp h CPPI_RAM) CPPI_RAM`` (fn l => PAT_ASSUM ``BD_QUEUE t (read_ndp h CPPI_RAM') CPPI_RAM'`` (fn r => ASSUME_TAC (CONJ l r))) THEN
   MATCH_MP_ASM_IMP_TAC ``P /\ Q`` BD_QUEUE_IMP_EQ_START_BD_PA_lemma THEN
   ASM_REWRITE_TAC []);

val MEM_BD_QUEUE_NOT_ZERO_lemma = store_thm (
  "MEM_BD_QUEUE_NOT_ZERO_lemma",
  ``!q start_bd_pa bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q
    ==>
    bd_pa <> 0w``,
  Induct_on `q` THENL
  [
   REWRITE_TAC [listTheory.MEM]
   ,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [BD_QUEUE_def, listTheory.MEM] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   Cases_on `bd_pa = h` THENL
   [
    REFLECT_ASM_TAC ``bd_pa = h`` THEN
    ASM_RW_ASM_TAC ``h = bd_pa`` ``h <> 0w`` THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``bd_pa <> h`` ``P \/ Q`` THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``read_ndp h CPPI_RAM``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] thm))))))) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val MEM_QUEUE_IMP_NOT_BD_QUEUE_NDP_MEM_lemma = store_thm (
  "MEM_QUEUE_IMP_NOT_BD_QUEUE_NDP_MEM_lemma",
  ``!q bd_pa CPPI_RAM.
    MEM bd_pa q
    ==>
    ~BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  CCONTR_TAC THEN
  RW_ASM_TAC ``~~P`` boolTheory.NOT_CLAUSES THEN
  ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``q : 32 word list``, ``read_ndp bd_pa CPPI_RAM``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] MEM_BD_QUEUE_NOT_ZERO_lemma)))))) THEN
  PAT_ASSUM ``bd_pa <> 0w`` (fn l => PAT_ASSUM ``BD_QUEUE q a m`` (fn r => ASSUME_TAC (CONJ l r) THEN ASSUME_TAC r)) THEN
  RW_ASM_TAC ``P /\ Q`` (GSYM (REWRITE_RULE [] (SPECL [``bd_pa: 32 word``, ``q : 32 word list``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] (CONJUNCT2 BD_QUEUE_def)))) THEN
  PAT_ASSUM ``BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM`` (fn l => PAT_ASSUM ``MEM a q`` (fn r => ASSUME_TAC (CONJ l r))) THEN
  MATCH_MP_ASM_IMP_TAC ``P /\ Q`` HEAD_IN_BD_QUEUE_NO_BD_QUEUE_lemma THEN
  ASM_RW_ASM_TAC ``BD_QUEUE (bd_pa::q) bd_pa CPPI_RAM`` ``¬BD_QUEUE (bd_pa::q) bd_pa CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val NOT_MEMBER_TAIL_lemma = store_thm (
  "NOT_MEMBER_TAIL_lemma",
  ``!q bd_pa CPPI_RAM.
    BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM
    ==>
    ~MEM bd_pa q``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  CCONTR_TAC THEN
  RW_ASM_TAC ``~~P`` boolTheory.NOT_CLAUSES THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL MEM_QUEUE_IMP_NOT_BD_QUEUE_NDP_MEM_lemma)) THEN
  ASM_RW_ASM_TAC ``BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM`` ``~BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM`` THEN
  UNDISCH_TAC ``F`` THEN
  REWRITE_TAC []);

val BD_QUEUE_MEMBER_IMP_NOT_EMPTY_PREFIX_lemma = store_thm (
 "BD_QUEUE_MEMBER_IMP_NOT_EMPTY_PREFIX_lemma",
 ``!q q' q'' start_bd_pa bd_pa CPPI_RAM.
   BD_QUEUE q'' (read_ndp bd_pa CPPI_RAM) CPPI_RAM /\
   MEM bd_pa q /\
   (q = q' ++ q'')
   ==>
   ?h t. q' = h::t``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL (SPEC ``q'' : 32 word list`` NOT_MEMBER_TAIL_lemma))) THEN
  ASM_RW_ASM_TAC ``q = q' ++ q''`` ``MEM bd_pa q`` THEN
  RW_ASM_TAC ``MEM bd_pa (q' ++ q'')`` listTheory.MEM_APPEND THEN
  ASM_RW_ASM_TAC ``¬MEM bd_pa q''`` ``P \/ Q`` THEN
  Cases_on `q'` THENL
  [
   RW_ASM_TAC ``MEM bd_pa []`` listTheory.MEM THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   EXISTS_TAC ``h: 32 word`` THEN
   EXISTS_TAC ``t: 32 word list`` THEN
   REWRITE_TAC []
  ]);

val BD_QUEUE_MEMBER_DISTINCT_START_IMP_NOT_EMPTY_PREFIX_lemma = store_thm (
 "BD_QUEUE_MEMBER_DISTINCT_START_IMP_NOT_EMPTY_PREFIX_lemma",
 ``!q q' q'' start_bd_pa bd_pa CPPI_RAM.
   BD_QUEUE q start_bd_pa CPPI_RAM /\
   BD_QUEUE q'' bd_pa CPPI_RAM /\
   bd_pa <> start_bd_pa /\
   (q = q' ++ q'')
   ==>
   ?h t. q' = h::t``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `q'` THENL
  [
   RW_ASM_TAC ``q = [] ++ q''`` listTheory.APPEND THEN
   ASM_RW_ASM_TAC ``q = q''`` ``BD_QUEUE q start_bd_pa CPPI_RAM`` THEN
   ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q'' : 32 word list``, ``start_bd_pa : 32 word``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_EQ_START_BD_PA_lemma)))) THEN
   ASM_RW_ASM_TAC ``start_bd_pa = bd_pa`` ``bd_pa <> start_bd_pa`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   EXISTS_TAC ``h: 32 word`` THEN
   EXISTS_TAC ``t: 32 word list`` THEN
   REWRITE_TAC []
  ]);

val BD_QUEUE_MEMBER_IMP_MEMBER_START_BD_PA_PREFIX_lemma = store_thm (
  "BD_QUEUE_MEMBER_IMP_MEMBER_START_BD_PA_PREFIX_lemma",
  ``!q q' q'' start_bd_pa bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q /\
    BD_QUEUE q'' (read_ndp bd_pa CPPI_RAM) CPPI_RAM /\
    (q = q' ++ q'')
    ==>
    MEM start_bd_pa q'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL BD_QUEUE_MEMBER_IMP_NOT_EMPTY_PREFIX_lemma)))) THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_RW_ASM_TAC ``q' = h::t`` ``q = q' ++ q''`` THEN
  RW_ASM_TAC ``q = h::t ++ q''`` listTheory.APPEND THEN
  ASM_RW_ASM_TAC ``q = h::(t ++ q'')`` ``BD_QUEUE q start_bd_pa CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa : 32 word``, ``t ++ q'' : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);







val EQ_BD_QUEUE_START_MEM_IMP_BD_QUEUE_MEM_START_lemma = store_thm (
  "EQ_BD_QUEUE_START_MEM_IMP_BD_QUEUE_MEM_START_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM' bd_pa.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa CPPI_RAM' /\
    MEM bd_pa q
    ==>
    ?q'.
    BD_QUEUE q' bd_pa CPPI_RAM /\
    BD_QUEUE q' bd_pa CPPI_RAM'``,
  Induct_on `q` THENL
  [
   REWRITE_TAC [listTheory.MEM]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``MEM bd_pa (h::q)`` listTheory.MEM THEN
   Cases_on `bd_pa = h` THENL
   [
    ASM_REWRITE_TAC [] THEN
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``h : bd_pa_type``, ``start_bd_pa : bd_pa_type``, ``q : bd_pa_type list``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
    ASM_REWRITE_TAC [] THEN
    EXISTS_TAC ``h::q : 32 word list`` THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
    RW_ASM_TAC ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM`` BD_QUEUE_def THEN
    RW_ASM_TAC ``BD_QUEUE (h::q) start_bd_pa CPPI_RAM'`` BD_QUEUE_def THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : 32 word list``, ``read_ndp h CPPI_RAM``, ``read_ndp h CPPI_RAM'``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_IMP_EQ_START_BD_PA_lemma)) THEN
    REFLECT_ASM_TAC ``read_ndp h CPPI_RAM = read_ndp h CPPI_RAM'`` THEN
    ASM_RW_ASM_TAC ``read_ndp h CPPI_RAM' = read_ndp h CPPI_RAM`` ``BD_QUEUE q (read_ndp h CPPI_RAM') CPPI_RAM'`` THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``read_ndp h CPPI_RAM``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``, ``bd_pa : bd_pa_type``] thm))) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val BD_QUEUE_MEM_IMP_EQ_NEXT_BD_PA_lemma = store_thm (
  "BD_QUEUE_MEM_IMP_EQ_NEXT_BD_PA_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM' bd_pa.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa CPPI_RAM' /\
    MEM bd_pa q
    ==>
    (read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_BD_QUEUE_START_MEM_IMP_BD_QUEUE_MEM_START_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL MEM_BD_QUEUE_NOT_ZERO_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q' : bd_pa_type list``, ``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  KEEP_ASM_RW_ASM_TAC ``q' = bd_pa::t`` ``BD_QUEUE q' bd_pa CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``q' = bd_pa::t`` ``BD_QUEUE q' bd_pa CPPI_RAM'`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : bd_pa_type``, ``t : bd_pa_type list``, ``bd_pa : bd_pa_type``, ``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_NON_EMPTY_IMP_EQ_NDP_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_DISTINCT_START_MEM_IMP_EQ_NEXT_BD_PA_lemma = store_thm (
  "BD_QUEUE_DISTINCT_START_MEM_IMP_EQ_NEXT_BD_PA_lemma",
  ``!q start_bd_pa start_bd_pa' CPPI_RAM CPPI_RAM' bd_pa.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa' CPPI_RAM' /\
    MEM bd_pa q
    ==>
    (read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (GSYM BD_QUEUE_IMP_EQ_START_BD_PA_lemma))) THEN
  ASM_RW_ASM_TAC ``start_bd_pa' = start_bd_pa`` ``BD_QUEUE q start_bd_pa' CPPI_RAM'`` THEN
  MATCH_MP_TAC BD_QUEUE_MEM_IMP_EQ_NEXT_BD_PA_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  EXISTS_TAC ``start_bd_pa : bd_pa_type`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_EQ_START_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_EQ_START_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM' bd_pa.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa CPPI_RAM' /\
    MEM bd_pa q
    ==>
    ?q.
    BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM /\
    BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_BD_QUEUE_START_MEM_IMP_BD_QUEUE_MEM_START_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL MEM_BD_QUEUE_NOT_ZERO_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q' : bd_pa_type list``, ``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  KEEP_ASM_RW_ASM_TAC ``q' = bd_pa::t`` ``BD_QUEUE q' bd_pa CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``q' = bd_pa::t`` ``BD_QUEUE q' bd_pa CPPI_RAM'`` THEN
  RW_ASM_TAC ``BD_QUEUE (bd_pa::t) bd_pa CPPI_RAM`` BD_QUEUE_def THEN
  RW_ASM_TAC ``BD_QUEUE (bd_pa::t) bd_pa CPPI_RAM'`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_MEM_IMP_EQ_NEXT_BD_PA_lemma)) THEN
  ASM_RW_ASM_TAC ``read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM`` ``BD_QUEUE t (read_ndp bd_pa CPPI_RAM') CPPI_RAM'`` THEN
  EXISTS_TAC ``t : 32 word list`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma",
  ``!q start_bd_pa start_bd_pa' CPPI_RAM CPPI_RAM' bd_pa.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa' CPPI_RAM' /\
    MEM bd_pa q
    ==>
    ?q.
    BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM /\
    BD_QUEUE q (read_ndp bd_pa CPPI_RAM) CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (GSYM BD_QUEUE_IMP_EQ_START_BD_PA_lemma))) THEN
  ASM_RW_ASM_TAC ``start_bd_pa' = start_bd_pa`` ``BD_QUEUE q start_bd_pa' CPPI_RAM'`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_EQ_START_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);















val NOT_OVERLAPPING_BD_QUEUE_MEMBERs_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma = store_thm (
  "NOT_OVERLAPPING_BD_QUEUE_MEMBERs_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma",
  ``!start_bd_pa bd_pa1 bd_pa2 l1 l2 CPPI_RAM.
    BD_QUEUE (l1 ++ l2) start_bd_pa CPPI_RAM /\
    ~BD_LIST_OVERLAP (l1 ++ l2) /\
    MEM bd_pa1 l1 /\
    MEM bd_pa2 l2
    ==>
    bd_pa1 <> bd_pa2``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPECL [``l1 ++ l2 : 32 word list``, ``start_bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_ALL_DISTINCT_lemma)) THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (SPECL [``bd_pa1 : 32 word``, ``bd_pa2 : 32 word``, ``l1 : 32 word list``, ``l2 : 32 word list``] ALL_DISTINCT_MEMBERS_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma))) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_MEMs_IMP_DISTINCT_MEMs_lemma = store_thm (
  "BD_QUEUE_MEMs_IMP_DISTINCT_MEMs_lemma",
  ``!bd_pa1 bd_pa2 q1 q2 start_bd_pa CPPI_RAM.
    BD_QUEUE (q1 ++ q2) start_bd_pa CPPI_RAM /\
    MEM bd_pa1 q1 /\
    MEM bd_pa2 q2
    ==>
    bd_pa1 <> bd_pa2``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC ALL_DISTINCT_MEMBERS_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma THEN
  EXISTS_TAC ``q1 : bd_pa_type list`` THEN
  EXISTS_TAC ``q2 : bd_pa_type list`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_ALL_DISTINCT_lemma THEN
  EXISTS_TAC ``start_bd_pa : bd_pa_type`` THEN
  EXISTS_TAC ``CPPI_RAM : cppi_ram_type`` THEN
  ASM_REWRITE_TAC []);



(***************************************************************)
(* Lemmas concerning modifications of buffer descriptor queue. *)
(***************************************************************)


val BD_QUEUE_IMP_SING_lemma = store_thm (
  "BD_QUEUE_IMP_SING_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM
    ==>
    SING {q | BD_QUEUE q start_bd_pa CPPI_RAM}``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [pred_setTheory.SING_DEF] THEN
  EXISTS_TAC ``q : 32 word list`` THEN
  REWRITE_TAC [pred_setTheory.EXTENSION] THEN
  GEN_TAC THEN
  REWRITE_TAC [pred_setTheory.GSPECIFICATION, pred_setTheory.IN_SING] THEN
  EQ_TAC THENL
  [
   DISCH_TAC THEN
   PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
   RW_ASM_TAC ``x = y`` (BETA_CONV ``(λq. (q,BD_QUEUE q a m)) x'``) THEN
   RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
   SPLIT_ASM_TAC THEN
   PAT_ASSUM ``BD_QUEUE q a m`` (fn l => PAT_ASSUM ``BD_QUEUE x' a m`` (fn r => ASSUME_TAC (CONJ l r))) THEN
   MATCH_MP_ASM_IMP_TAC ``P /\ Q`` EQ_START_EQ_QUEUEs_lemma THEN
   ASM_REWRITE_TAC []
   ,
   DISCH_TAC THEN
   EXISTS_TAC ``q : 32 word list`` THEN
   BETA_TAC THEN
   ASM_REWRITE_TAC [pairTheory.PAIR_EQ]
  ]);

val MEMBER_OF_BD_QUEUE_IS_START_OF_SUBQUEUE_lemma = store_thm (
  "MEMBER_OF_BD_QUEUE_IS_START_OF_SUBQUEUE_lemma",
  ``!q q1 bd_pa q2 start_bd_pa CPPI_RAM.
    (q = q1 ++ bd_pa::q2) /\
    BD_QUEUE q start_bd_pa CPPI_RAM
    ==>
    BD_QUEUE (bd_pa::q2) bd_pa CPPI_RAM``,
  Induct_on `q` THENL
  [
   REWRITE_TAC [listTheory.APPEND_eq_NIL, listTheory.NOT_CONS_NIL]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   Cases_on `q1` THENL
   [
    RW_ASM_TAC ``q = [] ++ bd_pa::q2`` listTheory.APPEND THEN
    ASM_RW_ASM_TAC ``q = bd_pa::q2`` ``BD_QUEUE q a m`` THEN
    PAT_ASSUM ``BD_QUEUE q a m`` (fn thm => ASSUME_TAC thm THEN ASSUME_TAC (MATCH_MP BD_QUEUE_IMP_HEAD_EQ_START_lemma thm)) THEN
    REFLECT_ASM_TAC ``bd_pa = start_bd_pa`` THEN
    ASM_RW_ASM_TAC ``start_bd_pa = bd_pa`` ``BD_QUEUE q a m`` THEN
    ASM_REWRITE_TAC []
    ,
    RW_ASM_TAC ``BD_QUEUE q a m`` BD_QUEUE_def THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``h::q = h'::t ++ bd_pa::q2`` listTheory.APPEND THEN
    RW_ASM_TAC ``h::q = h'::(t ++ bd_pa::q2)`` listTheory.CONS_11 THEN
    SPLIT_ASM_TAC THEN
    PAT_ASSUM ``q = t ++ bd_pa::q2`` (fn l => PAT_ASSUM ``BD_QUEUE q a m`` (fn r => ASSUME_TAC (CONJ l r))) THEN
    PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma = store_thm (
  "MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma",
  ``!q bd_pa start_bd_pa CPPI_RAM.
    MEM bd_pa q /\
    BD_QUEUE q start_bd_pa CPPI_RAM
    ==>
    ?q. BD_QUEUE q bd_pa CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``MEM bd_pa q`` listTheory.MEM_SPLIT THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  PAT_ASSUM ``x = y`` (fn l => PAT_ASSUM ``BD_QUEUE q a m`` (fn r => ASSUME_TAC (CONJ l r))) THEN
  PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP MEMBER_OF_BD_QUEUE_IS_START_OF_SUBQUEUE_lemma ant)) THEN
  EXISTS_TAC ``bd_pa::l2 : 32 word list`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma = store_thm (
  "BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma",
  ``!q start_bd_pa bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q
    ==>
    ?t. BD_QUEUE (bd_pa::t) bd_pa CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPEC_ALL MEM_BD_QUEUE_NOT_ZERO_lemma)))))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q' : 32 word list``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_RW_ASM_TAC ``q' = bd_pa::t`` ``BD_QUEUE q' bd_pa CPPI_RAM`` THEN
  EXISTS_TAC ``t : 32 word list`` THEN
  ASM_REWRITE_TAC []);







val bd_queue_def = Define `
  bd_queue (start_bd_pa : 32 word) (CPPI_RAM : 13 word -> 8 word) =
  CHOICE {q | BD_QUEUE q start_bd_pa CPPI_RAM}`;

val BD_QUEUE_IMP_bd_queue_lemma = store_thm (
  "BD_QUEUE_IMP_bd_queue_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM
    ==>
    (bd_queue start_bd_pa CPPI_RAM = q)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [bd_queue_def] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BD_QUEUE_IMP_SING_lemma)) THEN
  RW_ASM_TAC ``SING s`` pred_setTheory.SING_DEF THEN
  PAT_ASSUM ``P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``s1 = s2`` pred_setTheory.EXTENSION THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``x : 32 word list`` thm)) THEN
  RW_ASM_TAC ``m1 = m2`` pred_setTheory.IN_SING THEN
  RW_ASM_TAC ``x ∈ {q | BD_QUEUE q start_bd_pa CPPI_RAM}`` pred_setTheory.GSPECIFICATION THEN
  PAT_ASSUM ``P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``x = y`` (BETA_CONV ``(λq. (q,BD_QUEUE q start_bd_pa CPPI_RAM)) x'``) THEN
  RW_ASM_TAC ``x = y`` pairTheory.PAIR_EQ THEN
  ASM_REWRITE_TAC [pred_setTheory.CHOICE_SING] THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT2 thm)) THEN
  PAT_ASSUM ``BD_QUEUE q a m`` (fn l => PAT_ASSUM ``BD_QUEUE x' a m`` (fn r => ASSUME_TAC (CONJ l r))) THEN
  MATCH_MP_ASM_IMP_TAC ``P`` EQ_START_EQ_QUEUEs_lemma THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_IMP_EQ_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_IMP_EQ_BD_QUEUE_lemma",
  ``!q start_bd_pa start_bd_pa' CPPI_RAM CPPI_RAM'.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q start_bd_pa' CPPI_RAM'
    ==>
    (bd_queue start_bd_pa' CPPI_RAM' = bd_queue start_bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa' : bd_pa_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma = store_thm (
  "BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM
    ==>
    BD_QUEUE (bd_queue start_bd_pa CPPI_RAM) start_bd_pa CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_SPLIT_IMP_BD_QUEUE_SUFFIX_lemma = store_thm (
  "BD_QUEUE_SPLIT_IMP_BD_QUEUE_SUFFIX_lemma",
  ``!l1 l2 start_bd_pa CPPI_RAM.
    BD_QUEUE (l1 ++ l2) start_bd_pa CPPI_RAM
    ==>
    ?start_bd_pa'. BD_QUEUE l2 start_bd_pa' CPPI_RAM``,
  Induct_on `l1` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.APPEND] THEN
   DISCH_TAC THEN
   EXISTS_TAC ``start_bd_pa : 32 word`` THEN
   ASM_REWRITE_TAC []
   ,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.APPEND, BD_QUEUE_def] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``BD_QUEUE l a m`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
   ASM_REWRITE_TAC []
  ]);

val MEM_BD_QUEUE_IMP_START_BD_PA_NEQ_ZERO_lemma = store_thm (
  "MEM_BD_QUEUE_IMP_START_BD_PA_NEQ_ZERO_lemma",
  ``!q start_bd_pa bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q
    ==>
    start_bd_pa <> 0w``,
  REPEAT GEN_TAC THEN
  Cases_on `q` THENL
  [
   REWRITE_TAC [listTheory.MEM]
   ,
   REWRITE_TAC [BD_QUEUE_def] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   REFLECT_ASM_TAC ``h = start_bd_pa`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_QUEUE_START_MEMBER_OF_QUEUE_IMP_SUBQUEUE_lemma = store_thm (
  "BD_QUEUE_START_MEMBER_OF_QUEUE_IMP_SUBQUEUE_lemma",
  ``!q q' start_bd_pa start_bd_pa' CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q' start_bd_pa' CPPI_RAM /\
    MEM start_bd_pa' q
    ==>
    ?q''. q = q'' ++ q'``,
  Induct_on `q` THENL
  [
   REWRITE_TAC [listTheory.MEM]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   Cases_on `start_bd_pa' = h` THENL
   [
    EXISTS_TAC ``[] : 32 word list`` THEN
    REWRITE_TAC [listTheory.APPEND] THEN
    ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``start_bd_pa : 32 word``, ``q : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
    ASM_RW_ASM_TAC ``start_bd_pa' = h`` ``BD_QUEUE q' start_bd_pa' CPPI_RAM`` THEN
    ASM_RW_ASM_TAC ``h = start_bd_pa`` ``BD_QUEUE q' h CPPI_RAM`` THEN
    PAT_ASSUM ``BD_QUEUE (h::q) a m`` (fn l => PAT_ASSUM ``BD_QUEUE q a m`` (fn r => ASSUME_TAC (CONJ l r))) THEN
    PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP EQ_START_EQ_QUEUEs_lemma ant)) THEN
    ASM_REWRITE_TAC []
    ,
    RW_ASM_TAC ``MEM start_bd_pa' (h::q)`` listTheory.MEM THEN
    ASM_RW_ASM_TAC ``start_bd_pa' <> h`` ``P \/ Q`` THEN
    RW_ASM_TAC ``BD_QUEUE (h::q) a m`` BD_QUEUE_def THEN
    PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT2 (CONJUNCT2 thm))) THEN
    PAT_ASSUM ``BD_QUEUE q (read_ndp h CPPI_RAM) CPPI_RAM`` (fn c1 => PAT_ASSUM ``BD_QUEUE q' start_bd_pa' CPPI_RAM`` (fn c2 => PAT_ASSUM ``MEM start_bd_pa' q`` (fn c3 => ASSUME_TAC (LIST_CONJ [c1, c2, c3])))) THEN
    PAT_ASSUM ``!x.P`` (fn imp => PAT_ASSUM ``P /\ Q`` (fn ant => ASSUME_TAC (MATCH_MP imp ant))) THEN
    PAT_ASSUM ``P`` (fn thm => CHOOSE_TAC thm) THEN
    EXISTS_TAC ``h::q'' : 32 word list`` THEN
    ASM_REWRITE_TAC [listTheory.APPEND]
   ]
  ]);

val BD_QUEUE_START_NOT_ZERO_IMP_BD_QUEUE_EQ_START_TL_lemma = store_thm (
  "BD_QUEUE_START_NOT_ZERO_IMP_BD_QUEUE_EQ_START_TL_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    ?t. bd_queue start_bd_pa CPPI_RAM = start_bd_pa::t``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : 32 word list``, ``start_bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  EXISTS_TAC ``t : 32 word list`` THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_BD_QUEUE_BD_PA_NDP_IMP_BD_PA_IN_MIDDLE_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_BD_QUEUE_BD_PA_NDP_IMP_BD_PA_IN_MIDDLE_BD_QUEUE_lemma",
  ``!q q' start_bd_pa bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE q' (read_ndp bd_pa CPPI_RAM) CPPI_RAM /\
    MEM bd_pa q
    ==>
    ?q''. q = q'' ++ [bd_pa] ++ q'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [boolTheory.IMP_CLAUSES] (SPEC_ALL MEM_BD_QUEUE_NOT_ZERO_lemma))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (#1 (EQ_IMP_RULE (REWRITE_RULE [] (SPECL [``bd_pa : 32 word``, ``q' : 32 word list``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] (GSYM (CONJUNCT2 BD_QUEUE_def))))))) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : 32 word list``, ``bd_pa::q' : 32 word list``, ``start_bd_pa : 32 word``, ``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_START_MEMBER_OF_QUEUE_IMP_SUBQUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  EXISTS_TAC ``q'' : 32 word list`` THEN
  ASM_REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]);

val SUFFIX_EQ_BD_PA_NDPs_IMP_MEM_BD_PA_PREFIX_lemma = store_thm (
  "SUFFIX_EQ_BD_PA_NDPs_IMP_MEM_BD_PA_PREFIX_lemma",
  ``!q q' q'' start_bd_pa bd_pa CPPI_RAM.
    (q = q' ++ q'') /\
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q /\
    BD_QUEUE q'' (read_ndp bd_pa CPPI_RAM) CPPI_RAM
    ==>
    MEM bd_pa q'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `q'` THENL
  [
   RW_ASM_TAC ``q = [] ++ q''`` listTheory.APPEND THEN
   KEEP_ASM_RW_ASM_TAC ``q = q''`` ``MEM bd_pa q`` THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL (SPEC ``q'' : 32 word list`` MEM_QUEUE_IMP_NOT_BD_QUEUE_NDP_MEM_lemma))) THEN
   ASM_RW_ASM_TAC ``BD_QUEUE q'' (read_ndp bd_pa CPPI_RAM) CPPI_RAM`` ``~BD_QUEUE q'' (read_ndp bd_pa CPPI_RAM) CPPI_RAM`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL (SPECL [``q : 32 word list``, ``q'' : 32 word list``] BD_QUEUE_BD_QUEUE_BD_PA_NDP_IMP_BD_PA_IN_MIDDLE_BD_QUEUE_lemma))))) THEN
   PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
   ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q : 32 word list``, ``q''' ++ [bd_pa] : 32 word list``, ``h::t : 32 word list``, ``q'' : 32 word list``] (INST_TYPE [alpha |-> ``: 32 word``] EQ_SUFFIX_IMP_EQ_PREFIX_lemma))))) THEN
   ASM_RW_ASM_TAC ``q''' ++ [bd_pa] = h::t`` ``q = q''' ++ [bd_pa] ++ q''`` THEN
   ASM_RW_ASM_TAC ``q = h::t ++ q''`` ``MEM bd_pa q`` THEN
   RW_ASM_TAC ``MEM bd_pa (h::t ++ q'')`` listTheory.MEM_APPEND THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL (SPEC ``q'' : 32 word list`` NOT_MEMBER_TAIL_lemma))) THEN
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASM_REWRITE_TAC []
  ]);

val NOT_ZERO_START_BD_PA_BD_QUEUE_IMP_BD_QUEUE_START_BD_PA_NDP_QUEUE_lemma = store_thm (
  "NOT_ZERO_START_BD_PA_BD_QUEUE_IMP_BD_QUEUE_START_BD_PA_NDP_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    BD_QUEUE (bd_queue (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM) (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``q = start_bd_pa::t`` ``BD_QUEUE q start_bd_pa CPPI_RAM`` THEN
  RW_ASM_TAC ``BD_QUEUE (start_bd_pa::t) start_bd_pa CPPI_RAM`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPECL [``t : 32 word list``, ``read_ndp start_bd_pa CPPI_RAM``, ``CPPI_RAM : 13 word -> 8 word``] BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

























val BD_QUEUE_MEM_START_IMP_BD_QUEUE_TAIL_lemma = store_thm (
  "BD_QUEUE_MEM_START_IMP_BD_QUEUE_TAIL_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM start_bd_pa q
    ==>
    ?q. BD_QUEUE q (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``start_bd_pa : bd_pa_type``, ``t : bd_pa_type list``, ``CPPI_RAM : cppi_ram_type``]  BD_QUEUE_IMP_TL_BD_QUEUE_lemma)) THEN
  EXISTS_TAC ``t : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_START_NEQ_ZERO_IMP_BD_QUEUE_TAIL_lemma = store_thm (
  "BD_QUEUE_START_NEQ_ZERO_IMP_BD_QUEUE_TAIL_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    ?q. BD_QUEUE q (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_START_BD_PA_NEQ_ZERO_IMP_MEM_START_BD_PA_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_MEM_START_IMP_BD_QUEUE_TAIL_lemma)) THEN
  ASM_REWRITE_TAC []);






val BD_QUEUE_MEM_IMP_BD_QUEUE_SPLIT_lemma = store_thm (
  "BD_QUEUE_MEM_IMP_BD_QUEUE_SPLIT_lemma",
  ``!q start_bd_pa bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM bd_pa q
    ==>
    ?q' q''. (q = (q' ++ [bd_pa]) ++ q'') /\ BD_QUEUE q'' (read_ndp bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPECL [``bd_pa : bd_pa_type``, ``t : bd_pa_type list``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_IMP_TL_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (SPECL [``q : bd_pa_type list``, ``t : bd_pa_type list``] BD_QUEUE_BD_QUEUE_BD_PA_NDP_IMP_BD_PA_IN_MIDDLE_BD_QUEUE_lemma))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  EXISTS_TAC ``q'' : bd_pa_type list`` THEN
  EXISTS_TAC ``t : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_MEM_START_IMP_BD_QUEUE_TAIL_lemma = store_thm (
  "BD_QUEUE_MEM_START_IMP_BD_QUEUE_TAIL_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    MEM start_bd_pa q
    ==>
    ?q'. (q = [start_bd_pa] ++ q') /\ BD_QUEUE q' (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa::t : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] EQ_START_EQ_QUEUEs_lemma)) THEN
  EXISTS_TAC ``t : bd_pa_type list`` THEN
  RW_ASM_TAC ``BD_QUEUE (h::t) a m`` BD_QUEUE_def THEN
  ASM_REWRITE_TAC [listTheory.APPEND]);

val BD_QUEUE_START_NEQ_ZERO_IMP_BD_QUEUE_TAIL_lemma = store_thm (
  "BD_QUEUE_START_NEQ_ZERO_IMP_BD_QUEUE_TAIL_lemma",
  ``!q start_bd_pa CPPI_RAM.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    start_bd_pa <> 0w
    ==>
    ?q'. (q = [start_bd_pa] ++ q') /\ BD_QUEUE q' (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  EXISTS_TAC ``t : bd_pa_type list`` THEN
  KEEP_ASM_RW_ASM_TAC ``q = h::t`` ``BD_QUEUE q a m`` THEN
  RW_ASM_TAC ``BD_QUEUE (h::t) a m`` BD_QUEUE_def THEN
  ASM_REWRITE_TAC [listTheory.APPEND]);

val BD_QUEUE_DISTINCT_CPPI_RAM_IMP_SUFFIX_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_DISTINCT_CPPI_RAM_IMP_SUFFIX_BD_QUEUE_lemma",
  ``!q1 q2 bd_pa start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE (q1 ++ [bd_pa] ++ q2) start_bd_pa CPPI_RAM /\
    BD_QUEUE (q1 ++ [bd_pa] ++ q2) start_bd_pa CPPI_RAM'
    ==>
    BD_QUEUE q2 (read_ndp bd_pa CPPI_RAM) CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH ((SPEC_ALL o (SPECL [``q1 : bd_pa_type list``, ``bd_pa::q2 : bd_pa_type list``])) BD_QUEUE_SPLIT_IMP_BD_QUEUE_SUFFIX_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``q1 : bd_pa_type list``, ``bd_pa::q2 : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_SPLIT_IMP_BD_QUEUE_SUFFIX_lemma)) THEN
  REPEAT (PAT_ASSUM ``?x : bd_pa_type. P`` (fn thm => CHOOSE_TAC thm)) THEN
  RW_ASM_TAC ``BD_QUEUE (bd_pa::q2) start_bd_pa' CPPI_RAM'`` BD_QUEUE_def THEN
  RW_ASM_TAC ``BD_QUEUE (bd_pa::q2) start_bd_pa'' CPPI_RAM`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (GSYM (CONJ_ANT_TO_HYP (SPECL [``q2 : bd_pa_type list``, ``read_ndp bd_pa CPPI_RAM``, ``read_ndp bd_pa CPPI_RAM'``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_IMP_EQ_START_BD_PA_lemma))) THEN
  ASM_RW_ASM_TAC ``read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM`` ``BD_QUEUE q2 (read_ndp bd_pa CPPI_RAM') CPPI_RAM'`` THEN
  ASM_REWRITE_TAC []);


val BD_QUEUEs_DISJOINT_def = Define `BD_QUEUEs_DISJOINT q1 q2 = NO_BD_LIST_OVERLAP q1 q2`;

val _ = export_theory();
