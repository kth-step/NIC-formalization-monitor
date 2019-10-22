open HolKernel Parse boolLib bossLib;
open helperTactics;
open bdTheory;
open bd_queueTheory;
open bd_listTheory;
open cppi_ram_writesTheory;
open stateTheory;

(* This file contains definitions and lemmas concerning the preservation of q:
 * BD_QUEUE q start_bd_pa CPPI_RAM
 * ==>
 * BD_QUEUE q start_bd_pa CPPI_RAM'
 *)

val _ = new_theory "bd_queue_preservation_lemmas";

(**Start of fundemental definitions and lemmas of preservation of BD queues.**)

val BD_QUEUE_LOCATION_UNMODIFIED_def = Define `
  BD_QUEUE_LOCATION_UNMODIFIED q CPPI_RAM CPPI_RAM' =
  EVERY (\bd_pa. NDP_UNMODIFIED bd_pa CPPI_RAM CPPI_RAM') q`;

val BD_QUEUE_LOCATION_UNMODIFIED_IMP_SUFFIX_LOCATION_UNMODIFIED_lemma = store_thm (
  "BD_QUEUE_LOCATION_UNMODIFIED_IMP_SUFFIX_LOCATION_UNMODIFIED_lemma",
  ``!q1 q2 CPPI_RAM CPPI_RAM'.
    BD_QUEUE_LOCATION_UNMODIFIED (q1 ++ q2) CPPI_RAM CPPI_RAM'
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED q2 CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_LOCATION_UNMODIFIED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM, listTheory.MEM_APPEND] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BD_QUEUE_LOCATION_UNMODIFIED q CPPI_RAM CPPI_RAM'
    ==>
    BD_QUEUE q start_bd_pa CPPI_RAM'``,
  Induct_on `q` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [BD_QUEUE_def] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [BD_QUEUE_def, BD_QUEUE_LOCATION_UNMODIFIED_def, listTheory.EVERY_DEF] THEN
   REWRITE_TAC [GSYM BD_QUEUE_LOCATION_UNMODIFIED_def] THEN
   BETA_TAC THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_REWRITE_TAC [] THEN
   KEEP_ASM_RW_ASM_TAC ``h = start_bd_pa`` ``BD_QUEUE q (read_ndp h CPPI_RAM) CPPI_RAM`` THEN
   ASM_RW_ASM_TAC ``h = start_bd_pa`` ``NDP_UNMODIFIED h CPPI_RAM CPPI_RAM'`` THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL (SPEC ``start_bd_pa : 32 word`` NDP_UNMODIFIED_IMP_EQ_NDP_lemma))) THEN
   ASM_RW_ASM_TAC ``read_ndp start_bd_pa CPPI_RAM = read_ndp start_bd_pa CPPI_RAM'`` ``BD_QUEUE q (read_ndp start_bd_pa CPPI_RAM) CPPI_RAM`` THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``read_ndp start_bd_pa CPPI_RAM'``, ``CPPI_RAM : 13 word -> 8 word``, ``CPPI_RAM' : 13 word -> 8 word``] thm))) THEN
   ASM_REWRITE_TAC []
  ]);













val BD_QUEUE_PRESERVED_def = Define `
  BD_QUEUE_PRESERVED (BD_PROPERTY : 32 word -> (13 word -> 8 word) -> bool)
                     (q : 32 word list)
                     (CPPI_RAM : 13 word -> 8 word)
                     (CPPI_RAM' : 13 word -> 8 word) =
  EVERY (\bd_pa. BD_PRESERVED BD_PROPERTY bd_pa CPPI_RAM CPPI_RAM' \/ BD_EQ bd_pa CPPI_RAM CPPI_RAM') q`;

val BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma = store_thm (
  "BD_QUEUE_BD_PROPERTY_PRESERVATION_lemma",
  ``!BD_PROPERTY q CPPI_RAM CPPI_RAM'.
    BD_PROPERTY_DEPENDS_ONLY_ON_BD BD_PROPERTY /\
    EVERY (\bd_pa. BD_PROPERTY bd_pa CPPI_RAM) q /\
    BD_QUEUE_PRESERVED BD_PROPERTY q CPPI_RAM CPPI_RAM'
    ==>
    EVERY (\bd_pa. BD_PROPERTY bd_pa CPPI_RAM') q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_QUEUE_PRESERVED_def] THEN
  REWRITE_TAC [BD_PRESERVED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REPEAT DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P ==> Q \/ R`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  Cases_on `BD_PROPERTY e CPPI_RAM ⇒ BD_PROPERTY e CPPI_RAM'` THENL
  [
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
   ASM_RW_ASM_TAC ``BD_PROPERTY e CPPI_RAM`` ``BD_PROPERTY e CPPI_RAM ==> BD_PROPERTY e CPPI_RAM'`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
   RW_ASM_TAC ``BD_PROPERTY_DEPENDS_ONLY_ON_BD BD_PROPERTY`` BD_PROPERTY_DEPENDS_ONLY_ON_BD_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL (SPEC ``e : 32 word`` thm)))) THEN
   ASM_RW_ASM_TAC ``BD_PROPERTY e CPPI_RAM ⇔ BD_PROPERTY e CPPI_RAM'`` ``BD_PROPERTY e CPPI_RAM`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma = store_thm (
  "BD_WRITE_PRESERVES_BD_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_QUEUE_PROPERTY_lemma",
  ``!cppi_ram_update BD_PROPERTY q bd_pa CPPI_RAM CPPI_RAM'.
    BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY cppi_ram_update BD_PROPERTY /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    MEM bd_pa q /\
    (CPPI_RAM' = cppi_ram_update CPPI_RAM bd_pa)
    ==>
    BD_QUEUE_PRESERVED BD_PROPERTY q CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_QUEUE_PRESERVED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  RW_ASM_TAC ``BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY cppi_ram_update BD_PROPERTY`` BD_WRITE_PRESERVES_BD_QUEUE_PROPERTY_def THEN
  SPLIT_ASM_TAC THEN
  Cases_on `bd_pa = e` THENL
  [
   RW_ASM_TAC ``BD_WRITE_PRESERVES_BD_PROPERTY cppi_ram_update BD_PROPERTY`` BD_WRITE_PRESERVES_BD_PROPERTY_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
   KEEP_ASM_RW_ASM_TAC ``bd_pa = e`` ``BD_PRESERVED BD_PROPERTY bd_pa CPPI_RAM CPPI_RAM'`` THEN
   ASM_REWRITE_TAC []
   ,
   RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa : 32 word``, ``e : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] thm)) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
   ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : 32 word``, ``q : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
   ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM e`` ``P ==> Q`` THEN
   RW_ASM_TAC ``¬BD_LIST_OVERLAP q`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``e : 32 word``, ``bd_pa : 32 word``] thm)) THEN
   ASM_RW_ASM_TAC ``MEM e q`` ``P /\ Q ==> R`` THEN
   ASM_RW_ASM_TAC ``MEM bd_pa q`` ``P /\ Q ==> R`` THEN
   REFLECT_ASM_TAC ``bd_pa <> e`` THEN
   ASM_RW_ASM_TAC ``e <> bd_pa`` ``~P ==> R`` THEN
   ASM_RW_ASM_TAC ``~BDs_OVERLAP e bd_pa`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_AP_QUEUE_PRESERVED_def = Define `
  BD_AP_QUEUE_PRESERVED BD_AP_PROPERTY q CPPI_RAM CPPI_RAM' AP =
  EVERY (\bd_pa. BD_AP_PRESERVED BD_AP_PROPERTY bd_pa CPPI_RAM CPPI_RAM' AP \/
                 BD_EQ bd_pa CPPI_RAM CPPI_RAM') q`;

val BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_AP_QUEUE_PROPERTY_lemma = store_thm (
  "BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_IMP_PRESERVES_NON_OVERLAPPING_BD_AP_QUEUE_PROPERTY_lemma",
  ``!cppi_ram_update BD_AP_PROPERTY q bd_pa CPPI_RAM CPPI_RAM' AP.
    BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY cppi_ram_update BD_AP_PROPERTY AP /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    MEM bd_pa q /\
    (CPPI_RAM' = cppi_ram_update CPPI_RAM bd_pa)
    ==>
    BD_AP_QUEUE_PRESERVED BD_AP_PROPERTY q CPPI_RAM CPPI_RAM' AP``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_AP_QUEUE_PRESERVED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  Cases_on `bd_pa = e` THENL
  [
   RW_ASM_TAC ``BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY cppi_ram_update BD_AP_PROPERTY AP`` BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY_def THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY cppi_ram_update BD_AP_PROPERTY AP`` BD_AP_WRITE_PRESERVES_BD_AP_PROPERTY_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
   KEEP_ASM_RW_ASM_TAC ``bd_pa = e`` ``CPPI_RAM' = cppi_ram_update CPPI_RAM bd_pa`` THEN
   ASM_RW_ASM_TAC ``bd_pa = (e : 32 word)`` ``BD_AP_PRESERVED BD_AP_PROPERTY bd_pa CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa) AP`` THEN
   ASM_REWRITE_TAC []
   ,
   RW_ASM_TAC ``BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY cppi_ram_update BD_AP_PROPERTY AP`` BD_AP_WRITE_PRESERVES_BD_AP_QUEUE_PROPERTY_def THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``q : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : 32 word``, ``q : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
   RW_ASM_TAC ``~BD_LIST_OVERLAP q`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
   PAT_ASSUM ``!x y. P /\ Q ==> R`` (fn thm => ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (GSYM (SPECL [``e : 32 word``, ``bd_pa : 32 word``] thm))))) THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``e : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] thm))) THEN
   ASM_REWRITE_TAC []
  ]);

val BD_AP_QUEUE_BD_AP_PROPERTY_PRESERVATION_lemma = store_thm (
  "BD_AP_QUEUE_BD_AP_PROPERTY_PRESERVATION_lemma",
  ``!BD_AP_PROPERTY q CPPI_RAM CPPI_RAM' AP.
    BD_AP_PROPERTY_DEPENDS_ONLY_ON_BD_AP BD_AP_PROPERTY AP /\
    EVERY (λbd_pa. BD_AP_PROPERTY bd_pa CPPI_RAM AP) q /\
    BD_AP_QUEUE_PRESERVED BD_AP_PROPERTY q CPPI_RAM CPPI_RAM' AP
    ==>
    EVERY (λbd_pa. BD_AP_PROPERTY bd_pa CPPI_RAM' AP) q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  RW_ASM_TAC ``BD_AP_QUEUE_PRESERVED BD_AP_PROPERTY q CPPI_RAM CPPI_RAM' AP`` BD_AP_QUEUE_PRESERVED_def THEN
  RW_ASM_TAC ``EVERY P l`` listTheory.EVERY_MEM THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  PAT_ASSUM ``(\x.b) e`` (fn thm => ASSUME_TAC thm THEN UNDISCH_TAC (concl thm)) THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  Cases_on `BD_EQ e CPPI_RAM CPPI_RAM'`  THENL
  [
   RW_ASM_TAC ``BD_AP_PROPERTY_DEPENDS_ONLY_ON_BD_AP BD_AP_PROPERTY AP`` BD_AP_PROPERTY_DEPENDS_ONLY_ON_BD_AP_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL (SPEC ``e : 32 word`` thm)))) THEN
   REFLECT_ASM_TAC ``x = y`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   RW_ASM_TAC ``BD_AP_PRESERVED BD_AP_PROPERTY e CPPI_RAM CPPI_RAM' AP`` BD_AP_PRESERVED_def THEN
   ASM_RW_ASM_TAC ``BD_AP_PROPERTY e CPPI_RAM AP`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_WRITE_PREFIX_PRESERVES_BD_PROPERTY_SUFFIX_lemma = store_thm (
  "BD_WRITE_PREFIX_PRESERVES_BD_PROPERTY_SUFFIX_lemma",
  ``!start_bd_pa bd_pa l1 l2 cppi_ram_update BD_PROPERTY CPPI_RAM CPPI_RAM'.
    BD_QUEUE (l1 ++ l2) start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM (l1 ++ l2) /\
    ~BD_LIST_OVERLAP (l1 ++ l2) /\
    MEM bd_pa l1 /\
    BD_WRITE cppi_ram_update /\
    (CPPI_RAM' = cppi_ram_update CPPI_RAM bd_pa)
    ==>
    BD_QUEUE_PRESERVED BD_PROPERTY l2 CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_QUEUE_PRESERVED_def, listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (SPECL [``start_bd_pa : 32 word``, ``bd_pa : 32 word``, ``e : 32 word``, ``l1 : 32 word list``, ``l2 : 32 word list``, ``CPPI_RAM : 13 word -> 8 word``] NOT_OVERLAPPING_BD_QUEUE_MEMBERs_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [ASSUME ``MEM (bd_pa : 32 word) l1``, listTheory.MEM_APPEND] (DISCH ``MEM (bd_pa : 32 word) l1`` (SPECL [``bd_pa : 32 word``, ``l1 ++ l2 : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)))) THEN
  ASSUME_TAC (UNDISCH (REWRITE_RULE [ASSUME ``MEM (e : 32 word) l2``, listTheory.MEM_APPEND] (DISCH ``MEM (e : 32 word) l2`` (SPECL [``e : 32 word``, ``l1 ++ l2 : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)))) THEN
  RW_ASM_TAC ``~BD_LIST_OVERLAP (l1 ++ l2)`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
  PAT_ASSUM ``!x y. A /\ B /\ C ==> D`` (fn thm => (ASSUME_TAC (UNDISCH (REWRITE_RULE [listTheory.MEM_APPEND, ASSUME ``MEM (bd_pa : 32 word) l1``, ASSUME ``MEM (e : 32 word) l2``] (SPECL [``bd_pa : 32 word``, ``e : 32 word``] (ASSUME ``∀bd_pa1 bd_pa2. MEM bd_pa1 (l1 ++ l2) ∧ MEM bd_pa2 (l1 ++ l2) ∧ bd_pa1 ≠ bd_pa2 ⇒ ¬BDs_OVERLAP bd_pa1 bd_pa2``)))))) THEN
  RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
  PAT_ASSUM ``~BDs_OVERLAP bd_pa e`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SPECL [``bd_pa : 32 word``, ``e : 32 word``] BDs_OVERLAP_SYM_lemma] thm)) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``e : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] thm))) THEN
  ASM_REWRITE_TAC []);

val BD_WRITE_HEAD_PRESERVES_BD_PROPERTY_TAIL_lemma = store_thm (
  "BD_WRITE_HEAD_PRESERVES_BD_PROPERTY_TAIL_lemma",
  ``!start_bd_pa h t cppi_ram_update BD_PROPERTY CPPI_RAM CPPI_RAM'.
    BD_QUEUE (h::t) start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM (h::t) /\
    ~BD_LIST_OVERLAP (h::t) /\
    BD_WRITE cppi_ram_update /\
    (CPPI_RAM' = cppi_ram_update CPPI_RAM h)
    ==>
    BD_QUEUE_PRESERVED BD_PROPERTY t CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [rich_listTheory.CONS_APPEND] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (REWRITE_RULE [listTheory.MEM] (SPEC_ALL (SPECL [``start_bd_pa : 32 word``, ``h : 32 word``, ``[h : 32 word]``, ``t : 32 word list``] BD_WRITE_PREFIX_PRESERVES_BD_PROPERTY_SUFFIX_lemma)))) THEN
  ASM_REWRITE_TAC []);

val BD_WRITE_OUTSIDE_QUEUE_PRESERVES_BD_PROPERTY_lemma = store_thm (
  "BD_WRITE_OUTSIDE_QUEUE_PRESERVES_BD_PROPERTY_lemma",
  ``!cppi_ram_update BD_PROPERTY q bd_pa CPPI_RAM CPPI_RAM'.
    BD_WRITE cppi_ram_update /\
    BDs_IN_CPPI_RAM q /\
    BD_IN_CPPI_RAM bd_pa /\
    BD_NOT_OVERLAP_BDs bd_pa q /\
    (CPPI_RAM' = cppi_ram_update CPPI_RAM bd_pa)
    ==>
    BD_QUEUE_PRESERVED BD_PROPERTY q CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_QUEUE_PRESERVED_def, listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : bd_pa_type``, ``e : bd_pa_type``, ``q : bd_pa_type list``] BD_NOT_OVERLAP_BDs_IMP_BDs_NOT_OVERLAP_lemma)) THEN
  RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : 32 word``, ``q : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
  PAT_ASSUM ``~BDs_OVERLAP bd_pa e`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SPECL [``bd_pa : 32 word``, ``e : 32 word``] BDs_OVERLAP_SYM_lemma] thm)) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``e : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] thm))) THEN
  ASM_REWRITE_TAC []);

val WRITE_NON_OVERLAPPING_BD_QUEUE_HEAD_IMP_BD_PROPERTY_TAIL_PRESERVED_lemma = store_thm (
  "WRITE_NON_OVERLAPPING_BD_QUEUE_HEAD_IMP_BD_PROPERTY_TAIL_PRESERVED_lemma",
  ``!cppi_ram_update BD_PROPERTY h t start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE (h::t) start_bd_pa CPPI_RAM /\
    ~BD_LIST_OVERLAP (h::t) /\
    BDs_IN_CPPI_RAM (h::t) /\
    BD_WRITE cppi_ram_update /\
    (CPPI_RAM' = cppi_ram_update CPPI_RAM h)
    ==>
    BD_QUEUE_PRESERVED BD_PROPERTY t CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPECL [``h::t : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_ALL_DISTINCT_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``h : bd_pa_type``, ``t : bd_pa_type list``] NOT_BD_LIST_OVERLAP_ALL_DISTINCT_IMP_HD_NOT_OVERLAP_TL_lemma)) THEN
  RW_ASM_TAC ``BDs_IN_CPPI_RAM (h::t)`` BDs_IN_CPPI_RAM_HD_TL_EQ_lemma THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``cppi_ram_update : (13 word -> 8 word) -> 32 word -> 13 word -> 8 word``, ``BD_PROPERTY : 32 word -> (13 word -> 8 word) -> bool``, ``t : 32 word list``, ``h : 32 word``, ``CPPI_RAM : 13 word -> 8 word``, ``CPPI_RAM' : 13 word -> 8 word``] BD_WRITE_OUTSIDE_QUEUE_PRESERVES_BD_PROPERTY_lemma)) THEN
  ASM_REWRITE_TAC []);









val BD_QUEUE_NOT_LIST_OVERLAP_IMP_SINGLETON_LIST_NO_OVERLAP_lemma = store_thm (
  "BD_QUEUE_NOT_LIST_OVERLAP_IMP_SINGLETON_LIST_NO_OVERLAP_lemma",
  ``!h t start_bd_pa CPPI_RAM.
    BD_QUEUE (h::t) start_bd_pa CPPI_RAM /\
    ~BD_LIST_OVERLAP (h::t)
    ==>
    NO_BD_LIST_OVERLAP [h] t``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NO_BD_LIST_OVERLAP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  BETA_TAC THEN
  RW_ASM_TAC ``~P`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``e : bd_pa_type``, ``h : bd_pa_type``] thm)) THEN
  RW_ASM_TAC ``P ==> Q`` listTheory.MEM THEN
  KEEP_ASM_RW_ASM_TAC ``MEM e t`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``h::t : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_ALL_DISTINCT_lemma)) THEN
  RW_ASM_TAC ``ALL_DISTINCT l`` listTheory.ALL_DISTINCT THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``MEM e t`` listTheory.MEM_SPLIT THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  ASM_RW_ASM_TAC ``x = y`` ``~MEM h t`` THEN
  RW_ASM_TAC ``~P`` listTheory.MEM_APPEND THEN
  RW_ASM_TAC ``~P`` boolTheory.DE_MORGAN_THM THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``~MEM h (e::l2)`` listTheory.MEM THEN
  RW_ASM_TAC ``~(P \/ Q)`` boolTheory.DE_MORGAN_THM THEN
  SPLIT_ASM_TAC THEN
  REFLECT_ASM_TAC ``h <> e`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_NOT_BD_LIST_OVERLAP_IMP_NO_BD_SPLIT_OVERLAP_lemma = store_thm (
  "BD_QUEUE_NOT_BD_LIST_OVERLAP_IMP_NO_BD_SPLIT_OVERLAP_lemma",
  ``!q1 q2 start_bd_pa CPPI_RAM.
    BD_QUEUE (q1 ++ q2) start_bd_pa CPPI_RAM /\
    ~BD_LIST_OVERLAP (q1 ++ q2)
    ==>
    NO_BD_LIST_OVERLAP q1 q2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma, NO_BD_LIST_OVERLAP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM, listTheory.MEM_APPEND] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def, listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e' : bd_pa_type``, ``e : bd_pa_type``, ``q1 : bd_pa_type list``, ``q2 : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] BD_QUEUE_MEMs_IMP_DISTINCT_MEMs_lemma)) THEN
  REFLECT_ASM_TAC ``e' <> e`` THEN
  ASM_REWRITE_TAC []);













(**END OF LEMMAS CONCERNING CPPI_RAM_WRITE_STEPS IMPLYING CPPI_RAM_WRITE**)



(**START OF LEMMAS CONCERNING CPPI_RAM_WRITE_STEPs PRESERVATION OF BD_QUEUE**)


val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVE_NDPs_OF_BD_QUEUE_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVE_NDPs_OF_BD_QUEUE_lemma",
  ``!q cppi_ram_write_step_bd_pas bd_pa.
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas) /\
    MEM bd_pa q
    ==>
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN

  (* Reduces the goal to the assumptions of the lemma. *)
  MATCH_MP_TAC CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVES_NDP_OF_NON_OVERLAPPING_OR_WRITTEN_BD_lemma THEN

  (* Establishes assumption 1. *)
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (SPECL [``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``] LIST_MEMBER_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_LIST_lemma))) THEN

  (* Establishes assumption 2. *)
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``, ``bd_pa : bd_pa_type``] IN_NON_OVERLAPPING_LIST_IMP_NOT_OVERLAPPING_SUBLIST_OR_IN_SUBLIST_lemma)) THEN

  (* Establishes assumption 3. *)
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_IN_CPPI_RAM_BD_QUEUE_IMP_BD_IN_CPPI_RAM_lemma)) THEN

  (* Establishes assumption 4. *)
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``] IN_LIST1_IMP_IN_LIST2_AND_LIST2_IN_CPPI_RAM_IMP_LIST1_IN_CPPI_RAM_lemma)) THEN

  (* Assumptions 5 and 6 are already assumed. *)

  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_NDPs_OF_BD_QUEUE_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_NDPs_OF_BD_QUEUE_lemma",
  ``!q cppi_ram_write_step_bd_pas bd_pa.
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas) /\
    MEM bd_pa q
    ==>
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN

  (* Reduces the goal to the assumptions of the lemma. *)
  MATCH_MP_TAC CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_PRESERVES_NDP_OF_NON_OVERLAPPING_OR_WRITTEN_BD_lemma THEN

  (* Establishes assumption 1. *)
  ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (CONJ_ANT_TO_HYP (SPECL [``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``] LIST_MEMBER_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_LIST_lemma))) THEN

  (* Establishes assumption 2. *)
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``, ``bd_pa : bd_pa_type``] IN_NON_OVERLAPPING_LIST_IMP_NOT_OVERLAPPING_SUBLIST_OR_IN_SUBLIST_lemma)) THEN

  (* Establishes assumption 3. *)
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_IN_CPPI_RAM_BD_QUEUE_IMP_BD_IN_CPPI_RAM_lemma)) THEN

  (* Establishes assumption 4. *)
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``] IN_LIST1_IMP_IN_LIST2_AND_LIST2_IN_CPPI_RAM_IMP_LIST1_IN_CPPI_RAM_lemma)) THEN

  (* Assumptions 5 and 6 are already assumed. *)

  ASM_REWRITE_TAC []);




val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVE_BD_QUEUE_LOCATION_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVE_BD_QUEUE_LOCATION_lemma",
  ``!q CPPI_RAM cppi_ram_write_step_bd_pas.
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED q CPPI_RAM (reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_QUEUE_LOCATION_UNMODIFIED_def, listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVE_NDPs_OF_BD_QUEUE_lemma) THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_LOCATION_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_LOCATION_lemma",
  ``!q CPPI_RAM cppi_ram_write_step_bd_pas.
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED q CPPI_RAM (cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_QUEUE_LOCATION_UNMODIFIED_def, listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_NDPs_OF_BD_QUEUE_lemma) THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);


















val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_REVERSED_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_REVERSED_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM cppi_ram_write_step_bd_pas.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE q start_bd_pa (reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma THEN
  EXISTS_TAC ``CPPI_RAM : cppi_ram_type`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVE_BD_QUEUE_LOCATION_lemma THEN
  ASM_REWRITE_TAC []);



val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM cppi_ram_write_step_bd_pas.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE q start_bd_pa (cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma THEN
  EXISTS_TAC ``CPPI_RAM : cppi_ram_type`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_LOCATION_lemma THEN
  ASM_REWRITE_TAC []);

(**END OF LEMMAS CONCERNING CPPI_RAM_WRITE_STEPs PRESERVATION OF BD_QUEUE**)
















(**START OF LEMMAS CONCERNING NIC_DELTA PRESERVATION OF BD_QUEUE**)

val NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def = Define `
  NIC_DELTA_NOT_EXPANDS_BD_QUEUE
   (nic_delta : nic_delta_type)
   (nic : nic_state)
   (start_bd_pa_pre : bd_pa_type)
   (start_bd_pa_post : bd_pa_type) =
  IN_LIST1_IMP_IN_LIST2
    (bd_queue start_bd_pa_post (nic_delta nic).regs.CPPI_RAM)
    (bd_queue start_bd_pa_pre nic.regs.CPPI_RAM)`;

val NIC_DELTA_PRESERVES_CPPI_RAM_def = Define `
  NIC_DELTA_PRESERVES_CPPI_RAM (nic_delta : nic_state -> nic_state) (nic : nic_state) =
  ((nic_delta nic).regs.CPPI_RAM = nic.regs.CPPI_RAM)`;

val NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def = Define `
  NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs
  (nic_delta : nic_delta_type)
  (nic : nic_state)
  (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)
  =
  ((nic_delta nic).regs.CPPI_RAM = cppi_ram_write nic.regs.CPPI_RAM cppi_ram_write_step_bd_pas)`;

val PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def = Define `
  PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION
  (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)
  =
  CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)`;

val CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
  (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)
  (q : bd_pa_type list)
  =
  IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q`;

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def = Define `
  NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q =
  NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas /\
  CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas q /\
  PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas`;

val BD_NOT_OVERLAP_BD_QUEUE_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_IMP_BD_NOT_OVERLAP_WRITTEN_BDs_lemma = store_thm (
  "BD_NOT_OVERLAP_BD_QUEUE_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_IMP_BD_NOT_OVERLAP_WRITTEN_BDs_lemma",
  ``!bd_pa q cppi_ram_write_step_bd_pas.
    BD_NOT_OVERLAP_BDs bd_pa q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas q
    ==>
    BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE w a`` CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def THEN
  MATCH_MP_TAC BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_SUBLIST_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_NIC_DELTA_PRESERVES_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_NIC_DELTA_PRESERVES_BD_QUEUE_lemma",
  ``!(nic_delta : nic_delta_type) nic q start_bd_pa cppi_ram_write_step_bd_pas.
    BD_QUEUE q start_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas) /\
    ((nic_delta nic).regs.CPPI_RAM = cppi_ram_write nic.regs.CPPI_RAM cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE q start_bd_pa (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVES_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_BD_QUEUE_lemma",
  ``!nic_delta nic q start_bd_pa cppi_ram_write_step_bd_pas.
    BD_QUEUE q start_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q
    ==>
    BD_QUEUE q start_bd_pa (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_NIC_DELTA_PRESERVES_BD_QUEUE_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic cppi_ram_write_step_bd_pas`` NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas q`` CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def THEN
  RW_ASM_TAC ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION cppi_ram_write_step_bd_pas`` PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED q nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_LOCATION_lemma THEN
  ASM_REWRITE_TAC []);


(* How to prove that q in BD_QUEUE q start_bd_pa CPPI_RAM is preserved by a
   CPPI_RAM write by cppi_ram_write:
   1. Prove that nic_delta writes CPPI_RAM according to the sequence of
      (cppi_ram_write_step, bd_pa) pairs in cppi_ram_step_bd_pas:
      NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta cppi_ram_write_step_bd_pas
   2. Prove that each bd_pa in cppi_ram_write_step_bd_pas is in q:
      CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE
   3. Prove that each cppi_ram_write_step in cppi_ram_write_step_bd_pas writes
      the BD at the corresponding address: CPPI_RAM_WRITE_STEP_WRITES_BD_def.
   4. Prove that each cppi_ram_write_step in cppi_ram_write_step_bd_pas
      preserves the NDP field of the BD at the corresponding address:
      CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def.
   5. Use 3. and 4. to prove:
      PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def
   6. Apply NIC_DELTA_PRESERVEs_BD_QUEUE_lemma. *)














val BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma = store_thm (
  "BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    EQ_BDs q CPPI_RAM CPPI_RAM'
    ==>
    BD_QUEUE q start_bd_pa CPPI_RAM'``,
  Induct_on `q` THENL
  [
   REWRITE_TAC [BD_QUEUE_def] THEN
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [BD_QUEUE_def, EQ_BDs_HD_TL_EQ_BD_EQ_HD_EQ_BDs_TL_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``read_ndp h CPPI_RAM``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] thm))) THEN
   ASM_REWRITE_TAC [] THEN
   ASSUME_TAC (GSYM (UNDISCH (SPECL [``h : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_EQ_IMP_EQ_NDP_lemma))) THEN
   ASM_RW_ASM_TAC ``read_ndp h CPPI_RAM = read_ndp h CPPI_RAM'`` ``BD_QUEUE q (read_ndp h CPPI_RAM) CPPI_RAM'`` THEN
   ASM_RW_ASM_TAC ``h = start_bd_pa`` ``BD_QUEUE q (read_ndp h CPPI_RAM') CPPI_RAM'`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_QUEUE_EQ_BDs_IMP_EQ_BD_QUEUEs_lemma = store_thm (
  "BD_QUEUE_EQ_BDs_IMP_EQ_BD_QUEUEs_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    EQ_BDs q CPPI_RAM CPPI_RAM'
    ==>
    (bd_queue start_bd_pa CPPI_RAM' = bd_queue start_bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val EQ_BDs_IMP_NO_BD_LIST_OVERLAP_PRESERVED_lemma = store_thm (
  "EQ_BDs_IMP_NO_BD_LIST_OVERLAP_PRESERVED_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM'.
    BD_QUEUE (bd_queue start_bd_pa CPPI_RAM) start_bd_pa CPPI_RAM /\
    EQ_BDs (bd_queue start_bd_pa CPPI_RAM) CPPI_RAM CPPI_RAM' /\
    NO_BD_LIST_OVERLAP q (bd_queue start_bd_pa CPPI_RAM)
    ==>
    NO_BD_LIST_OVERLAP q (bd_queue start_bd_pa CPPI_RAM')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_queue start_bd_pa CPPI_RAM``, ``start_bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_EQ_BDs_IMP_EQ_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDPS_OF_BDs_IMP_EQ_CPPI_RAM_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDPS_OF_BDs_IMP_EQ_CPPI_RAM_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q
    ==>
    ((nic_delta nic).regs.CPPI_RAM = cppi_ram_write nic.regs.CPPI_RAM cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_IMP_CPPI_RAM_WRITE_WRITES_BDs_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_IMP_CPPI_RAM_WRITE_WRITES_BDs_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q
    ==>
    CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_EQ_STEPs_WRITE_BD_AND_STEPs_PRESERVE_NDP_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL CPPI_RAM_WRITE_STEPs_WRITE_BD_IMP_CPPI_RAM_WRITE_WRITES_BDs_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_WRITTEN_BDs_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_WRITTEN_BDs_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q bd_pa.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    BD_NOT_OVERLAP_BDs bd_pa q
    ==>
    BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC BD_NOT_OVERLAP_BD_QUEUE_CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_IMP_BD_NOT_OVERLAP_WRITTEN_BDs_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_BDs_IN_CPPI_RAM_IMP_SUBLIST_BDs_IN_CPPI_RAM_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_BDs_IN_CPPI_RAM_IMP_SUBLIST_BDs_IN_CPPI_RAM_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    BDs_IN_CPPI_RAM q
    ==>
    BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_AND_LIST2_IN_CPPI_RAM_IMP_LIST1_IN_CPPI_RAM_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_DISJOINT_FROM_BD_IMP_BD_PRESERVED_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_DISJOINT_FROM_BD_IMP_BD_PRESERVED_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q bd_pa.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    BD_IN_CPPI_RAM bd_pa /\
    BDs_IN_CPPI_RAM q /\
    BD_NOT_OVERLAP_BDs bd_pa q
    ==>
    BD_EQ bd_pa nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_FIELDs_NOT_NDPS_OF_BDs_IMP_EQ_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC is_eq THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_IMP_CPPI_RAM_WRITE_WRITES_BDs_lemma)) THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas`` CPPI_RAM_WRITE_WRITES_BDs_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_BDs_IN_CPPI_RAM_IMP_SUBLIST_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_WRITTEN_BDs_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma",
  ``!q1 q2 nic_delta nic cppi_ram_write_step_bd_pas.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q1 /\
    BDs_IN_CPPI_RAM q1 /\
    BDs_IN_CPPI_RAM q2 /\
    NO_BD_LIST_OVERLAP q1 q2
    ==>
    EQ_BDs q2 nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_DISJOINT_FROM_BD_IMP_BD_PRESERVED_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  EXISTS_TAC ``q1 : bd_pa_type list`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : bd_pa_type``, ``q2 : bd_pa_type list``] BD_IN_CPPI_RAM_BD_QUEUE_IMP_BD_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL (SPECL [``e : bd_pa_type``] MEM_NO_BD_LIST_OVERLAP_IMP_BD_NOT_OVERLAP_BDs_lemma))) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BD_PRESERVES_NON_OVERLAPPING_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BD_PRESERVES_NON_OVERLAPPING_BD_QUEUE_lemma",
  ``!bd_pa q nic_delta nic cppi_ram_write_step_bd_pas.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas [bd_pa] /\
    BD_IN_CPPI_RAM bd_pa /\
    BDs_IN_CPPI_RAM q /\
    BD_NOT_OVERLAP_BDs bd_pa q
    ==>
    EQ_BDs q nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  Q.EXISTS_TAC `[bd_pa]` THEN
  Q.EXISTS_TAC `cppi_ram_write_step_bd_pas` THEN
  REWRITE_TAC [GSYM BD_NOT_OVERLAP_BDs_EQ_NO_BD_LIST_OVERLAP_lemma] THEN
  REWRITE_TAC [GSYM BD_IN_CPPI_RAM_EQ_BD_SINGLETON_IN_CPPI_RAM_lemma] THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_HEAD_OF_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_EQ_TAIL_BDs_lemma = store_thm (
  "NIC_DELTA_WRITES_HEAD_OF_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_EQ_TAIL_BDs_lemma",
  ``!h t start_bd_pa nic nic_delta cppi_ram_write_step_bd_pas.
    BD_QUEUE (h::t) start_bd_pa nic.regs.CPPI_RAM /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas [h] /\
    BDs_IN_CPPI_RAM (h::t) /\
    ~BD_LIST_OVERLAP (h::t)
    ==>
    EQ_BDs t nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``[h : bd_pa_type]`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  RW_ASM_TAC ``BDs_IN_CPPI_RAM q`` (SPECL [``h : bd_pa_type``, ``t : bd_pa_type list``] BDs_IN_CPPI_RAM_HD_TL_EQ_lemma) THEN
  ASM_REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_DEF] THEN
  MATCH_MP_TAC BD_QUEUE_NOT_LIST_OVERLAP_IMP_SINGLETON_LIST_NO_OVERLAP_lemma THEN
  EXISTS_TAC ``start_bd_pa : bd_pa_type`` THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_NIC_DELTA_WRITES_DISJOINT_QUEUE_IMP_BD_QUEUE_PRESERVED_lemma = store_thm (
  "BD_QUEUE_NIC_DELTA_WRITES_DISJOINT_QUEUE_IMP_BD_QUEUE_PRESERVED_lemma",
  ``!q1 q2 start_bd_pa nic nic_delta cppi_ram_write_step_bd_pas.
    BD_QUEUE q2 start_bd_pa nic.regs.CPPI_RAM /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q1 /\
    BDs_IN_CPPI_RAM q1 /\
    BDs_IN_CPPI_RAM q2 /\
    NO_BD_LIST_OVERLAP q1 q2
    ==>
    BD_QUEUE q2 start_bd_pa (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``q1 : bd_pa_type list`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_NIC_DELTA_WRITES_DSIJOINT_QUEUE_IMP_BD_QUEUE_PRESERVED2_lemma = store_thm (
  "BD_QUEUE_NIC_DELTA_WRITES_DSIJOINT_QUEUE_IMP_BD_QUEUE_PRESERVED2_lemma",
  ``!q1 q2 start_bd_pa nic nic_delta cppi_ram_write_step_bd_pas.
    BD_QUEUE q2 start_bd_pa nic.regs.CPPI_RAM /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q1 /\
    BDs_IN_CPPI_RAM q1 /\
    BDs_IN_CPPI_RAM q2 /\
    NO_BD_LIST_OVERLAP q1 q2
    ==>
    (bd_queue start_bd_pa (nic_delta nic).regs.CPPI_RAM = bd_queue start_bd_pa nic.regs.CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC BD_QUEUE_IMP_EQ_BD_QUEUE_lemma THEN
  EXISTS_TAC ``q2 : bd_pa_type list`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_NIC_DELTA_WRITES_DISJOINT_QUEUE_IMP_BD_QUEUE_PRESERVED_lemma THEN
  EXISTS_TAC ``q1 : bd_pa_type list`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

(* End of lemmas about independence of two disjoint queues. *)













(* Lemmas used to preserve queue when SOP is updated by reception. *)

val BD_QUEUE_NOT_OVERLAPPING_IN_CPPI_RAM_AND_WRITTEN_PRESERVED_NDPs_IMP_BD_QUEUE_PRESERVED_lemma = store_thm (
  "BD_QUEUE_NOT_OVERLAPPING_IN_CPPI_RAM_AND_WRITTEN_PRESERVED_NDPs_IMP_BD_QUEUE_PRESERVED_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM' cppi_ram_write_step_bd_pas.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas) /\
    (CPPI_RAM' = cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)
    ==>
    BD_QUEUE q start_bd_pa CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_AND_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_CPPI_RAM_WRITE_PRESERVE_BD_QUEUE_LOCATION_lemma)) THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_RW_ASM_TAC ``x = y`` ``BD_QUEUE_LOCATION_UNMODIFIED q m m'`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_QUEUE_IN_CPPI_RAM_NON_OVERLAPPING_WRITTEN_PRESERVED_NDPs_MEM_Q_IMP_BD_QUEUE_NEXT_MEM_lemma = store_thm (
  "BD_QUEUE_IN_CPPI_RAM_NON_OVERLAPPING_WRITTEN_PRESERVED_NDPs_MEM_Q_IMP_BD_QUEUE_NEXT_MEM_lemma",
  ``!q start_bd_pa CPPI_RAM CPPI_RAM' cppi_ram_write_step_bd_pas bd_pa.
    BD_QUEUE q start_bd_pa CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas) /\
    (CPPI_RAM' = cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas) /\
    MEM bd_pa q
    ==>
    ?q. BD_QUEUE q (read_ndp bd_pa CPPI_RAM) (cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_NOT_OVERLAPPING_IN_CPPI_RAM_AND_WRITTEN_PRESERVED_NDPs_IMP_BD_QUEUE_PRESERVED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``bd_pa : bd_pa_type``, ``CPPI_RAM' : cppi_ram_type``] BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL BD_QUEUE_MEM_IMP_EQ_NEXT_BD_PA_lemma)) THEN
  RW_ASM_TAC ``BD_QUEUE (h::t) a m`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM`` ``BD_QUEUE t (read_ndp bd_pa CPPI_RAM') CPPI_RAM'`` THEN
  EXISTS_TAC ``t : bd_pa_type list`` THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_REWRITE_TAC []);










val NIC_DELTA_MEM_NON_OVERLAPPING_BD_QUEUE_IMP_PRESERVES_SUFFIX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_MEM_NON_OVERLAPPING_BD_QUEUE_IMP_PRESERVES_SUFFIX_BD_QUEUE_lemma",
  ``!q start_bd_pa bd_pa nic nic_delta cppi_ram_write_step_bd_pas.
    BD_QUEUE q start_bd_pa nic.regs.CPPI_RAM /\
    MEM bd_pa q /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q
    ==>
    ?q' q''. (q = (q' ++ [bd_pa]) ++ q'') /\ BD_QUEUE q'' (read_ndp bd_pa nic.regs.CPPI_RAM) (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa : bd_pa_type``, ``bd_pa : bd_pa_type``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEM_IMP_BD_QUEUE_SPLIT_lemma)) THEN
  REPEAT (PAT_ASSUM ``?x : bd_pa_type list. P`` (fn thm => CHOOSE_TAC thm)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  KEEP_ASM_RW_ASM_TAC ``q = q'`` ``BD_QUEUE q start_bd_pa nic.regs.CPPI_RAM`` THEN
  KEEP_ASM_RW_ASM_TAC ``q = q'`` ``BD_QUEUE q start_bd_pa (nic_delta nic).regs.CPPI_RAM`` THEN
  EXISTS_TAC ``q' : bd_pa_type list`` THEN
  EXISTS_TAC ``q'' : bd_pa_type list`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_DISTINCT_CPPI_RAM_IMP_SUFFIX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``q' : bd_pa_type list`` THEN
  EXISTS_TAC ``start_bd_pa : bd_pa_type`` THEN
  ASM_REWRITE_TAC []);




val NIC_DELTA_PRESERVES_START_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_START_BD_PA_CPPI_RAM_IMP_NOT_EXPANDS_BD_QUEUE_lemma",
  ``!start_bd_pa_pre start_bd_pa_post nic_delta nic.
    (start_bd_pa_post = start_bd_pa_pre) /\
    NIC_DELTA_PRESERVES_CPPI_RAM nic_delta nic
    ==>
    NIC_DELTA_NOT_EXPANDS_BD_QUEUE nic_delta nic start_bd_pa_pre start_bd_pa_post``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_CPPI_RAM_def] THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val NIC_DELTA_START_BD_PA_POST_EQ_ZERO_IMP_NOT_EXPANDS_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_START_BD_PA_POST_EQ_ZERO_IMP_NOT_EXPANDS_BD_QUEUE_lemma",
  ``!nic_delta nic start_bd_pa_pre start_bd_pa_post.
    (start_bd_pa_post = 0w)
    ==>
    NIC_DELTA_NOT_EXPANDS_BD_QUEUE nic_delta nic start_bd_pa_pre start_bd_pa_post``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPEC ``(nic_delta (nic : nic_state)).regs.CPPI_RAM`` BD_QUEUE_EMPTY_START_ZERO_lemma) THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_RW_ASM_TAC ``x = y`` ``BD_QUEUE [] 0w m`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``[] : bd_pa_type list``, ``start_bd_pa_post : bd_pa_type``, ``(nic_delta (nic : nic_state)).regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def] THEN
  ASM_REWRITE_TAC [IN_EMPTY_LIST_IMP_IN_LIST_lemma]);

val NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_IMP_NOT_EXPANDS_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_IMP_NOT_EXPANDS_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas start_bd_pa_pre start_bd_pa_post q.
    BD_QUEUE q start_bd_pa_pre nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    (q = bd_queue start_bd_pa_pre nic.regs.CPPI_RAM) /\
    (start_bd_pa_post = start_bd_pa_pre)
    ==>
    NIC_DELTA_NOT_EXPANDS_BD_QUEUE nic_delta nic start_bd_pa_pre start_bd_pa_post``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic w q`` NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic w`` NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE w q`` CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def THEN
  RW_ASM_TAC ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION w`` PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic_delta : nic_delta_type``, ``nic : nic_state``, ``q : bd_pa_type list``, ``start_bd_pa_pre : bd_pa_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` ] NIC_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  REFLECT_ASM_TAC ``start_bd_pa_post = start_bd_pa_pre : bd_pa_type`` THEN
  ASM_RW_ASM_TAC ``start_bd_pa_pre = start_bd_pa_post`` ``BD_QUEUE q start_bd_pa_pre (nic_delta nic).regs.CPPI_RAM`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa_pre : bd_pa_type``, ``start_bd_pa_post : bd_pa_type``, ``nic.regs.CPPI_RAM``, ``(nic_delta (nic : nic_state)).regs.CPPI_RAM``] BD_QUEUE_IMP_EQ_BD_QUEUE_lemma)) THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def] THEN
  ASM_REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_REFL_lemma]);

val NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_START_BD_PA_POST_IN_PRE_BD_QUEUE_IMP_NOT_EXPANDS_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_START_BD_PA_POST_IN_PRE_BD_QUEUE_IMP_NOT_EXPANDS_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas start_bd_pa_pre start_bd_pa_post q.
    BD_QUEUE q start_bd_pa_pre nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    MEM start_bd_pa_post q /\
    (q = bd_queue start_bd_pa_pre nic.regs.CPPI_RAM)
    ==>
    NIC_DELTA_NOT_EXPANDS_BD_QUEUE nic_delta nic start_bd_pa_pre start_bd_pa_post``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic w q`` NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs nic_delta nic w`` NIC_DELTA_CPPI_RAM_WRITE_EQ_CPPI_RAM_WRITE_STEP_BD_PAs_def THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE w q`` CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def THEN
  RW_ASM_TAC ``PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION w`` PRESERVES_NON_OVERLAPPING_BD_QUEUE_LOCATION_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic_delta : nic_delta_type``, ``nic : nic_state``, ``q : bd_pa_type list``, ``start_bd_pa_pre : bd_pa_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` ] NIC_DELTA_CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa_pre : bd_pa_type``, ``start_bd_pa_post : bd_pa_type``, ``(nic_delta (nic : nic_state)).regs.CPPI_RAM``] BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``start_bd_pa_post::t : bd_pa_type list``, ``start_bd_pa_pre : bd_pa_type``, ``start_bd_pa_post : bd_pa_type``, ``(nic_delta (nic : nic_state)).regs.CPPI_RAM``] BD_QUEUE_START_MEMBER_OF_QUEUE_IMP_SUBQUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (SYM (UNDISCH (SPECL [``start_bd_pa_post::t : bd_pa_type list``, ``start_bd_pa_post : bd_pa_type``, ``(nic_delta (nic : nic_state)).regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma))) THEN
  ASM_RW_ASM_TAC ``start_bd_pa_post::t = bd_queue a m`` ``q = q'' ++ h::t`` THEN
  ASM_RW_ASM_TAC ``q = q'' ++ bd_queue a m`` ``q = bd_queue a m`` THEN
  REWRITE_TAC [NIC_DELTA_NOT_EXPANDS_BD_QUEUE_def] THEN
  REFLECT_ASM_TAC ``q'' ++ q = q'`` THEN
  PAT_ASSUM ``bd_queue a m = q'' ++ bd_queue a' m'`` (fn thm => REWRITE_TAC [thm]) THEN
  REWRITE_TAC [IN_SUFFIX_IMP_IN_LIST_lemma]);







(*******Start of Lemmas only used for the transmission automaton***********)

val PRESERVES_NDP_def = Define `
  PRESERVES_NDP cppi_ram_update =
  !bd_pa CPPI_RAM.
NDP_UNMODIFIED bd_pa CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa)`;

val BD_WRITE_PRESERVES_NDP_def = Define `
  BD_WRITE_PRESERVES_NDP cppi_ram_update =
  BD_WRITE cppi_ram_update /\
  PRESERVES_NDP cppi_ram_update`;

val BD_WRITE_PRESERVES_NDP_OF_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma = store_thm (
  "BD_WRITE_PRESERVES_NDP_OF_NON_OVERLAPPING_CPPI_RAM_BD_QUEUE_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma",
  ``!cppi_ram_update q bd_pa CPPI_RAM.
    BD_WRITE_PRESERVES_NDP cppi_ram_update /\
    BDs_IN_CPPI_RAM q /\
    ~BD_LIST_OVERLAP q /\
    MEM bd_pa q
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED q CPPI_RAM (cppi_ram_update CPPI_RAM bd_pa)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_QUEUE_LOCATION_UNMODIFIED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `bd_pa = e` THENL
  [
   RW_ASM_TAC ``BD_WRITE_PRESERVES_NDP cppi_ram_update`` BD_WRITE_PRESERVES_NDP_def THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``PRESERVES_NDP cppi_ram_update`` PRESERVES_NDP_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL (SPEC ``e : 32 word`` thm))) THEN
   ASM_REWRITE_TAC []
   ,
   RW_ASM_TAC ``BD_WRITE_PRESERVES_NDP cppi_ram_update`` BD_WRITE_PRESERVES_NDP_def THEN
   PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT1 thm)) THEN
   RW_ASM_TAC ``BD_WRITE cppi_ram_update`` BD_WRITE_def THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``q : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``e : 32 word``, ``q : 32 word list``] BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma)) THEN
   RW_ASM_TAC ``¬BD_LIST_OVERLAP q`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON (SPECL [``bd_pa : 32 word``, ``e : 32 word``] thm)))))))) THEN
   PAT_ASSUM ``~BDs_OVERLAP bd_pa e`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] thm)) THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``bd_pa : 32 word``, ``e : 32 word``, ``CPPI_RAM : 13 word -> 8 word``] thm))) THEN
   ASSUME_TAC (UNDISCH (SPECL [``e : 32 word``, ``CPPI_RAM : 13 word -> 8 word``, ``(cppi_ram_update : (13 word -> 8 word) -> 32 word -> (13 word -> 8 word)) CPPI_RAM bd_pa``] BD_EQ_IMP_NDP_UNMODIFIED_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

(*******End of Lemmas only used for the transmission automaton***********)

val _ = export_theory();

