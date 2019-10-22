open HolKernel Parse boolLib bossLib;
open helperTactics;
open bdTheory;

val _ = new_theory "bd_list";

(*
 * True if and only if there is a pair of buffer descriptors in the given list
 * that overlap.
 *)
val BD_LIST_OVERLAP_def = Define `BD_LIST_OVERLAP (bd_pas : 32 word list) =
  ?bd_pa1 bd_pa2.
  MEM bd_pa1 bd_pas /\ MEM bd_pa2 bd_pas /\ bd_pa1 <> bd_pa2 /\
  BDs_OVERLAP bd_pa1 bd_pa2`;

val NO_OVERLAP_IMP_NO_OVERLAP_TAIL_lemma = store_thm (
  "NO_OVERLAP_IMP_NO_OVERLAP_TAIL_lemma",
  ``!h t.
    ~BD_LIST_OVERLAP (h::t)
    ==>
    ~BD_LIST_OVERLAP t``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_LIST_OVERLAP_def, listTheory.MEM] THEN
  DISCH_TAC THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (BETA_CONV ``(\bd_pa1. ?bd_pa2. ((bd_pa1 = h) ∨ MEM bd_pa1 t) ∧ ((bd_pa2 = h) ∨ MEM bd_pa2 t) ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2) bd_pa1``)] thm)) THEN
  RW_ASM_TAC ``P`` boolTheory.NOT_EXISTS_THM THEN
  RW_ASM_TAC ``P`` (BETA_CONV ``(λbd_pa1. ∃bd_pa2. ((bd_pa1 = h) ∨ MEM bd_pa1 t) ∧ ((bd_pa2 = h) ∨ MEM bd_pa2 t) ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2) x``) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (BETA_CONV ``(\bd_pa2. ((x = h) ∨ MEM x t) ∧ ((bd_pa2 = h) ∨ MEM bd_pa2 t) ∧ x ≠ bd_pa2 ∧ BDs_OVERLAP x bd_pa2) bd_pa2``)] thm)) THEN
  RW_ASM_TAC ``P`` boolTheory.NOT_EXISTS_THM THEN
  RW_ASM_TAC ``P`` (BETA_CONV ``(λbd_pa2. ((x = h) ∨ MEM x t) ∧ ((bd_pa2 = h) ∨ MEM bd_pa2 t) ∧ x ≠ bd_pa2 ∧ BDs_OVERLAP x bd_pa2) x'``) THEN
  RW_ASM_TAC ``P`` boolTheory.DE_MORGAN_THM THEN

  ONCE_REWRITE_TAC [SYM (BETA_CONV ``(\bd_pa1. ?bd_pa2. MEM bd_pa1 t ∧ MEM bd_pa2 t ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2) bd_pa1``)] THEN
  REWRITE_TAC [boolTheory.NOT_EXISTS_THM] THEN
  BETA_TAC THEN
  ONCE_REWRITE_TAC [SYM (BETA_CONV ``(\bd_pa2. MEM x t ∧ MEM bd_pa2 t ∧ x ≠ bd_pa2 ∧ BDs_OVERLAP x bd_pa2) bd_pa2``)] THEN
  REWRITE_TAC [boolTheory.NOT_EXISTS_THM] THEN
  BETA_TAC THEN

  REWRITE_TAC [boolTheory.DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  SPLIT_ASM_TAC THEN
  Cases_on `x ≠ h ∧ ¬MEM x t` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
  Cases_on `x' ≠ h ∧ ¬MEM x' t` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ALL_TAC
  ] THEN
  ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
  ASM_REWRITE_TAC []);

val NOT_BD_LIST_OVERLAP_IMP_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma = prove (
  ``!q.
    ~BD_LIST_OVERLAP q
    ==>
    !bd_pa1 bd_pa2.
    MEM bd_pa1 q /\ MEM bd_pa2 q /\ bd_pa1 <> bd_pa2
    ==>
    ~BDs_OVERLAP bd_pa1 bd_pa2``,
  GEN_TAC THEN
  DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``~BD_LIST_OVERLAP q`` BD_LIST_OVERLAP_def THEN
  PAT_ASSUM ``~P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (BETA_CONV ``(\bd_pa1. ?bd_pa2. MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2) bd_pa1``)] thm)) THEN
  RW_ASM_TAC ``~P`` boolTheory.NOT_EXISTS_THM THEN
  RW_ASM_TAC ``!x.P`` (BETA_CONV ``(λbd_pa1. ∃bd_pa2. MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2) x``) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (BETA_CONV ``(\bd_pa2. MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2) bd_pa2``)] thm)) THEN
  RW_ASM_TAC ``!x. P`` boolTheory.NOT_EXISTS_THM THEN
  RW_ASM_TAC ``!x. P`` (BETA_CONV ``(λbd_pa2. MEM x q ∧ MEM bd_pa2 q ∧ x ≠ bd_pa2 ∧ BDs_OVERLAP x bd_pa2) x'``) THEN
  PAT_ASSUM ``!x. P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa1 : 32 word``, ``bd_pa2 : 32 word``] thm)) THEN
  RW_ASM_TAC ``~P`` boolTheory.DE_MORGAN_THM THEN
  ASM_RW_ASM_TAC ``MEM bd_pa1 q`` ``P \/ Q`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa2 q`` ``P \/ Q`` THEN
  ASM_RW_ASM_TAC ``bd_pa1 <> bd_pa2`` ``P \/ Q`` THEN
  ASM_REWRITE_TAC []);

val ALL_DISTINCT_MEMBERS_NOT_OVERLAP_IMP_NOT_BD_LIST_OVERLAP_lemma = prove (
  ``!q.
    (!bd_pa1 bd_pa2.
     MEM bd_pa1 q /\ MEM bd_pa2 q /\ bd_pa1 <> bd_pa2
     ==>
     ~BDs_OVERLAP bd_pa1 bd_pa2)
    ==>
    ~BD_LIST_OVERLAP q``,
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [boolTheory.IMP_DISJ_THM] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM boolTheory.DE_MORGAN_THM] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (BETA_CONV ``(\bd_pa2.((MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2) ∧ BDs_OVERLAP bd_pa1 bd_pa2)) bd_pa2``)] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM boolTheory.NOT_EXISTS_THM] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [SYM (BETA_CONV ``(\bd_pa1. ∃x. (λbd_pa2. (MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2) ∧ BDs_OVERLAP bd_pa1 bd_pa2) x) bd_pa1``)] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM boolTheory.NOT_EXISTS_THM] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BETA_CONV ``(λbd_pa2. (MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2) ∧ BDs_OVERLAP bd_pa1 bd_pa2) x``] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BETA_CONV ``(λbd_pa1. ∃x. (MEM bd_pa1 q ∧ MEM x q ∧ bd_pa1 ≠ x) ∧ BDs_OVERLAP bd_pa1 x) x``] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (REWRITE_RULE [GSYM boolTheory.CONJ_ASSOC] thm)) THEN
  PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (REWRITE_RULE [SYM (SPEC ``q : 32 word list`` (ONCE_REWRITE_RULE [GEN_ALPHA_CONV ``x : 32 word`` ``?bd_pa1 x'. MEM bd_pa1 q ∧ MEM x' q ∧ bd_pa1 ≠ x' ∧ BDs_OVERLAP bd_pa1 x'``] (ONCE_REWRITE_RULE [GEN_ALPHA_CONV ``x' : 32 word`` ``?bd_pa2. MEM bd_pa1 q ∧ MEM bd_pa2 q ∧ bd_pa1 ≠ bd_pa2 ∧ BDs_OVERLAP bd_pa1 bd_pa2``] BD_LIST_OVERLAP_def)))] thm)) THEN
  ASM_REWRITE_TAC []);

val NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma = store_thm (
  "NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma",
  ``!q.
    ~BD_LIST_OVERLAP q
    =
    (!bd_pa1 bd_pa2.
     MEM bd_pa1 q /\ MEM bd_pa2 q /\ bd_pa1 <> bd_pa2
     ==>
     ~BDs_OVERLAP bd_pa1 bd_pa2)``,
  GEN_TAC THEN
  EQ_TAC THENL
  [
   REWRITE_TAC [NOT_BD_LIST_OVERLAP_IMP_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma]
   ,
   REWRITE_TAC [ALL_DISTINCT_MEMBERS_NOT_OVERLAP_IMP_NOT_BD_LIST_OVERLAP_lemma]
  ]);

val BD_LIST_HDs_EQ_lemma = store_thm (
  "BD_LIST_HDs_EQ_lemma",
  ``!h1 h2 t.
    ~BD_LIST_OVERLAP (h1::h2::t)
    =
    ~BD_LIST_OVERLAP (h2::h1::t)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma, listTheory.MEM] THEN
  REWRITE_TAC [boolTheory.DISJ_ASSOC] THEN
  EQ_TAC THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC [SPECL [``bd_pa1 = h2 : bd_pa_type``, ``bd_pa1 = h1 : bd_pa_type``] boolTheory.DISJ_SYM] THEN
  ASM_REWRITE_TAC []);

val DISTINCT_BD_PA_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_BDs_lemma = store_thm (
  "DISTINCT_BD_PA_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_BDs_lemma",
  ``!bd_pa1 bd_pa2 l.
    bd_pa1 <> bd_pa2 /\
    MEM bd_pa1 l /\
    ~BD_LIST_OVERLAP (bd_pa2::l)
    ==>
    ~BDs_OVERLAP bd_pa1 bd_pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma] THEN
  REWRITE_TAC [listTheory.MEM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (REWRITE_RULE [] (SPECL [``bd_pa1 : bd_pa_type``, ``bd_pa2 : bd_pa_type``] thm))) THEN
  ASM_RW_ASM_TAC ``bd_pa1 <> bd_pa2`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa1 l`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val NOT_BD_LIST_OVERLAP_APPEND_IMP_NOT_BD_LIST_OVERLAP_SUFFIX_lemma = store_thm (
  "NOT_BD_LIST_OVERLAP_APPEND_IMP_NOT_BD_LIST_OVERLAP_SUFFIX_lemma",
  ``!l1 l2.
    ~BD_LIST_OVERLAP (l1 ++ l2)
    ==>
    ~BD_LIST_OVERLAP l2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma] THEN
  DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x : bd_pa_type. P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC [listTheory.MEM_APPEND]);

(*
 * If all pointers are distinct, then the head is distinct from all members of
 * the tail.
 *)
val ALL_DISTINCT_IMP_EACH_MEMBER_OF_TAIL_NEQ_HEAD_lemma = store_thm (
  "ALL_DISTINCT_IMP_EACH_MEMBER_OF_TAIL_NEQ_HEAD_lemma",
  ``!(h : 32 word) (t : 32 word list).
    ALL_DISTINCT (h::t)
    ==>
    !e. MEM e t ==> e <> h``,
  Induct_on `t` THENL
  [
   REWRITE_TAC [listTheory.MEM]
   ,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   GEN_TAC THEN
   DISCH_TAC THEN
   Cases_on `e = h` THENL
   [
    ASM_REWRITE_TAC [] THEN
    ASM_RW_ASM_TAC ``e = h`` ``MEM e (h::t)`` THEN
    RW_ASM_TAC ``ALL_DISTINCT (h'::h::t)`` listTheory.ALL_DISTINCT THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``~MEM h' (h::t)`` listTheory.MEM THEN
    RW_ASM_TAC``¬((h' = h) ∨ MEM h' t)`` boolTheory.DE_MORGAN_THM THEN
    SPLIT_ASM_TAC THEN
    PAT_ASSUM ``h' ≠ h`` (fn thm => ASSUME_TAC (GSYM thm)) THEN
    ASM_REWRITE_TAC []
    ,
    PAT_ASSUM ``ALL_DISTINCT (h'::h::t)`` (fn thm => ASSUME_TAC (REWRITE_RULE [listTheory.ALL_DISTINCT] thm)) THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``~MEM h' (h::t)`` listTheory.MEM THEN
    RW_ASM_TAC ``¬((h' = h) ∨ MEM h' t)`` boolTheory.DE_MORGAN_THM THEN
    SPLIT_ASM_TAC THEN
    PAT_ASSUM ``¬MEM h' t`` (fn l => PAT_ASSUM ``ALL_DISTINCT t`` (fn r => ASSUME_TAC (CONJ l r))) THEN
    PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (REWRITE_RULE [GSYM listTheory.ALL_DISTINCT] thm)) THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``h' : 32 word`` thm))) THEN
    RW_ASM_TAC ``MEM e (h::t)`` listTheory.MEM THEN
    ASM_RW_ASM_TAC ``e <> h`` ``P \/ Q`` THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``e : 32 word`` thm))) THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val ALL_DISTINCT_MEMBERS_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma = store_thm (
  "ALL_DISTINCT_MEMBERS_IN_SPLITs_IMP_DISTINCT_MEMBERs_lemma",
  ``!(bd_pa1 : 32 word) bd_pa2 l1 l2.
    ALL_DISTINCT (l1 ++ l2) /\
    MEM bd_pa1 l1 /\
    MEM bd_pa2 l2
    ==>
    bd_pa1 <> bd_pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [listTheory.ALL_DISTINCT_APPEND] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa1 : 32 word`` thm))) THEN
  CCONTR_TAC THEN
  RW_ASM_TAC ``~~P`` boolTheory.NOT_CLAUSES THEN
  ASM_RW_ASM_TAC ``bd_pa1 = bd_pa2`` ``~MEM bd_pa1 l2`` THEN
  ASM_RW_ASM_TAC ``¬MEM bd_pa2 l2`` ``MEM bd_pa2 l2`` THEN
  ASM_REWRITE_TAC []);

val APPEND_CONS_ACYCLIC_lemma = store_thm (
  "APPEND_CONS_ACYCLIC_lemma",
  ``!l l1 h. l <> l1 ++ h::l``,
  Induct_on `l` THENL
  [
   REPEAT GEN_TAC THEN
   Cases_on `l1` THEN
   REWRITE_TAC [listTheory.APPEND, listTheory.NOT_NIL_CONS]
   ,
   REPEAT GEN_TAC THEN
   Cases_on `l1` THENL
   [
    REWRITE_TAC [listTheory.APPEND, listTheory.CONS_ACYCLIC]
    ,
    REWRITE_TAC [listTheory.APPEND] THEN
    PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (SPECL [``t ++ [h']``, ``h``] thm)) THEN
    RW_ASM_TAC ``P`` (GSYM listTheory.APPEND_ASSOC) THEN
    RW_ASM_TAC ``P`` listTheory.APPEND THEN
    ASSUME_TAC (UNDISCH (SPECL [``l : 'a list``, ``t ++ h'::h::l : 'a list``] listTheory.LIST_NOT_EQ)) THEN
    PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (SPECL [``h``, ``h''``] thm)) THEN
    ASM_REWRITE_TAC [listTheory.APPEND]
   ]
  ]);

val CONS_APPEND_ACYCLIC_lemma = store_thm (
  "CONS_APPEND_ACYCLIC_lemma",
  ``!l l1 h. l <> h::l1 ++ l``,
  Induct_on `l` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.APPEND, listTheory.NOT_NIL_CONS]
   ,
   REPEAT GEN_TAC THEN
   Cases_on `l1` THENL
   [
    REWRITE_TAC [listTheory.APPEND, listTheory.CONS_ACYCLIC]
    ,
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``t ++ [h]``, ``h''``] thm)) THEN
    RW_ASM_TAC ``P`` listTheory.APPEND THEN
    RW_ASM_TAC ``P`` (GSYM listTheory.APPEND_ASSOC) THEN
    RW_ASM_TAC ``P`` listTheory.APPEND THEN
    ASSUME_TAC (UNDISCH (SPECL [``l : 'a list``, ``h''::(t ++ h::l) : 'a list``] listTheory.LIST_NOT_EQ)) THEN
    ASM_REWRITE_TAC [listTheory.APPEND]
   ]
  ]);

val EQ_SUFFIX_IMP_EQ_PREFIX_lemma = store_thm (
  "EQ_SUFFIX_IMP_EQ_PREFIX_lemma",
  ``!l l1 l2 l3.
    (l = l1 ++ l3) /\
    (l = l2 ++ l3)
    ==>
    (l1 = l2)``,
  Induct_on `l` THENL
  [
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.APPEND_eq_NIL] THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   REPEAT GEN_TAC THEN
   Cases_on `l1`  THEN Cases_on `l2` THENL
   [
    REWRITE_TAC []
    ,
    DISCH_TAC THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``h::l = [] ++ l3`` listTheory.APPEND THEN
    ASM_RW_ASM_TAC ``h::l = l3`` ``h::l = h'::t ++ l3`` THEN
    RW_ASM_TAC ``l3 = h'::t ++ l3`` CONS_APPEND_ACYCLIC_lemma THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
    ,
    DISCH_TAC THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``h::l = [] ++ l3`` listTheory.APPEND THEN
    ASM_RW_ASM_TAC ``h::l = l3`` ``h::l = h'::t ++ l3`` THEN
    RW_ASM_TAC ``l3 = h'::t ++ l3`` CONS_APPEND_ACYCLIC_lemma THEN
    UNDISCH_TAC ``F`` THEN
    REWRITE_TAC []
    ,
    REWRITE_TAC [listTheory.APPEND, listTheory.CONS_11] THEN
    DISCH_TAC THEN
    SPLIT_ASM_TAC THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``t : 'a list``, ``t' : 'a list``, ``l3 : 'a list``] thm))))) THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT (WEAKEN_TAC (fn term => (type_of (#1 (dest_eq term))) = ``: 'a list``)) THEN
    ASM_RW_ASM_TAC ``h = h'`` ``h = h''`` THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val HD_TL_EQ_HD_APPEND_TL_lemma = store_thm (
  "HD_TL_EQ_HD_APPEND_TL_lemma",
  ``!h t. h::t = [h] ++ t``,
  REWRITE_TAC [listTheory.APPEND]);

val BDs_IN_CPPI_RAM_def = Define `
  BDs_IN_CPPI_RAM (bd_pas : 32 word list) =
  EVERY BD_IN_CPPI_RAM  bd_pas`;

val BDs_IN_CPPI_RAM_HD_TL_EQ_lemma = store_thm (
  "BDs_IN_CPPI_RAM_HD_TL_EQ_lemma",
  ``!bd_pa bd_pas.
    BDs_IN_CPPI_RAM (bd_pa::bd_pas) = BD_IN_CPPI_RAM bd_pa /\ BDs_IN_CPPI_RAM bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_DEF]);

val BDs_IN_CPPI_RAM_IMP_SUFFIX_BDs_IN_CPPI_RAM_lemma = store_thm (
  "BDs_IN_CPPI_RAM_IMP_SUFFIX_BDs_IN_CPPI_RAM_lemma",
  ``!l1 l2.
    BDs_IN_CPPI_RAM (l1 ++ l2)
    ==>
    BDs_IN_CPPI_RAM l2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def] THEN
  REWRITE_TAC [listTheory.EVERY_APPEND] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val BDs_IN_CPPI_RAM_IMP_PREFIX_BDs_IN_CPPI_RAM_lemma = store_thm (
  "BDs_IN_CPPI_RAM_IMP_PREFIX_BDs_IN_CPPI_RAM_lemma",
  ``!q1 q2 start_bd_pa CPPI_RAM.
    BDs_IN_CPPI_RAM (q1 ++ q2)
    ==>
    BDs_IN_CPPI_RAM q1``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM, listTheory.MEM_APPEND] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val BDs_IN_CPPI_RAM_IMP_SPLITs_IN_CPPI_RAM_lemma = store_thm (
  "BDs_IN_CPPI_RAM_IMP_SPLITs_IN_CPPI_RAM_lemma",
  ``!q1 q2.
    BDs_IN_CPPI_RAM (q1 ++ q2)
    ==>
    BDs_IN_CPPI_RAM q1 /\
    BDs_IN_CPPI_RAM q2``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL BDs_IN_CPPI_RAM_IMP_PREFIX_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``q1 : bd_pa_type list``, ``q2 : bd_pa_type list``] BDs_IN_CPPI_RAM_IMP_SUFFIX_BDs_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC []);

val BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma = store_thm (
  "BD_PA_IN_CPPI_RAM_LOCATED_BD_QUEUE_IMP_BD_PA_IN_CPPI_RAM_lemma",
  ``!bd_pa q.
    MEM bd_pa q /\
    BDs_IN_CPPI_RAM q
    ==>
    BD_IN_CPPI_RAM bd_pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : 32 word`` thm))) THEN
  ASM_REWRITE_TAC []);

val BD_IN_CPPI_RAM_IMP_BD_SINGLETON_IN_CPPI_RAM_lemma = store_thm (
  "BD_IN_CPPI_RAM_IMP_BD_SINGLETON_IN_CPPI_RAM_lemma",
  ``!bd_pa. BD_IN_CPPI_RAM bd_pa ==> BDs_IN_CPPI_RAM [bd_pa]``,
  GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_MEM, listTheory.MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val BD_IN_CPPI_RAM_EQ_BD_SINGLETON_IN_CPPI_RAM_lemma = store_thm (
  "BD_IN_CPPI_RAM_EQ_BD_SINGLETON_IN_CPPI_RAM_lemma",
  ``!bd_pa. BD_IN_CPPI_RAM bd_pa = BDs_IN_CPPI_RAM [bd_pa]``,
  GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_MEM, listTheory.MEM] THEN
  EQ_TAC THENL
  [
   DISCH_TAC THEN
   GEN_TAC THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
   ,
   DISCH_TAC THEN
   PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (REWRITE_RULE [] (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
   ASM_REWRITE_TAC []
  ]);

val BD_NOT_OVERLAP_BDs_def = Define `
  BD_NOT_OVERLAP_BDs (bd_pa : 32 word) (bd_pas : 32 word list) =
  EVERY (\bd_pa2. ~BDs_OVERLAP bd_pa bd_pa2) bd_pas`;

val BD_NOT_OVERLAP_BDs_IMP_BDs_NOT_OVERLAP_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_IMP_BDs_NOT_OVERLAP_lemma",
  ``!bd_pa1 bd_pa2 bd_pas.
    BD_NOT_OVERLAP_BDs bd_pa1 bd_pas /\
    MEM bd_pa2 bd_pas
    ==>
    ~BDs_OVERLAP bd_pa1 bd_pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa2 : 32 word`` thm))) THEN
  ASM_REWRITE_TAC []);

val NOT_BD_LIST_OVERLAP_ALL_DISTINCT_IMP_HD_NOT_OVERLAP_TL_lemma = store_thm (
  "NOT_BD_LIST_OVERLAP_ALL_DISTINCT_IMP_HD_NOT_OVERLAP_TL_lemma",
  ``!bd_pa bd_pas.
    ~BD_LIST_OVERLAP (bd_pa::bd_pas) /\
    ALL_DISTINCT (bd_pa::bd_pas)
    ==>
    BD_NOT_OVERLAP_BDs bd_pa bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma] THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa : bd_pa_type``, ``e : bd_pa_type``] thm)) THEN
  RW_ASM_TAC ``P ==> Q`` listTheory.MEM THEN
  KEEP_ASM_RW_ASM_TAC ``MEM e bd_pas`` ``P ==> Q`` THEN
  RW_ASM_TAC ``ALL_DISTINCT l`` listTheory.ALL_DISTINCT THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``~MEM bd_pa bd_pas`` (GSYM rich_listTheory.MEM_SING_APPEND) THEN
  RW_ASM_TAC ``MEM e t`` listTheory.MEM_SPLIT THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``l1 : bd_pa_type list``, ``l2 : bd_pa_type list``] thm)) THEN
  ASM_RW_ASM_TAC ``x = y`` ``x <> y`` THEN
  RW_ASM_TAC ``x <> y`` (GSYM listTheory.APPEND_ASSOC) THEN
  RW_ASM_TAC ``x <> y`` listTheory.APPEND THEN
  RW_ASM_TAC ``x <> y`` listTheory.APPEND_11 THEN
  RW_ASM_TAC ``x <> y`` listTheory.CONS_11 THEN
  REFLECT_ASM_TAC ``h <> e`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val BD_NOT_OVERLAP_BDs_HD_TL_EQ_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_HD_TL_EQ_lemma",
  ``!bd_pa1 bd_pa2 bd_pas.
    BD_NOT_OVERLAP_BDs bd_pa1 (bd_pa2::bd_pas) =
    ~BDs_OVERLAP bd_pa1 bd_pa2 /\ BD_NOT_OVERLAP_BDs bd_pa1 bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def, listTheory.EVERY_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC []);

val NO_BD_LIST_OVERLAP_def = Define `
  NO_BD_LIST_OVERLAP bd_pas1 bd_pas2 =
  EVERY (\bd_pa. BD_NOT_OVERLAP_BDs bd_pa bd_pas1) bd_pas2`;

val NO_BD_LIST_OVERLAP_SYM_lemma = store_thm (
  "NO_BD_LIST_OVERLAP_SYM_lemma",
  ``!q1 q2. NO_BD_LIST_OVERLAP q1 q2 = NO_BD_LIST_OVERLAP q2 q1``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NO_BD_LIST_OVERLAP_def] THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  EQ_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] (UNDISCH (SPEC ``e : bd_pa_type`` (UNDISCH (SPEC ``e' : bd_pa_type`` thm)))))) THEN
  ASM_REWRITE_TAC []);

val BD_NOT_OVERLAP_BDs_EQ_NO_BD_LIST_OVERLAP_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_EQ_NO_BD_LIST_OVERLAP_lemma",
  ``!bd_pa q. BD_NOT_OVERLAP_BDs bd_pa q = NO_BD_LIST_OVERLAP [bd_pa] q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NO_BD_LIST_OVERLAP_def] THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_DEF] THEN
  BETA_TAC THEN
  EQ_TAC THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC [BDs_OVERLAP_SYM_lemma] THEN
  ASM_REWRITE_TAC []);

val MEM_NO_BD_LIST_OVERLAP_IMP_BD_NOT_OVERLAP_BDs_lemma = store_thm (
  "MEM_NO_BD_LIST_OVERLAP_IMP_BD_NOT_OVERLAP_BDs_lemma",
  ``!bd_pa q1 q2.
    NO_BD_LIST_OVERLAP q1 q2 /\
    MEM bd_pa q2
    ==>
    BD_NOT_OVERLAP_BDs bd_pa q1``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  RW_ASM_TAC ``NO_BD_LIST_OVERLAP q1 q2`` NO_BD_LIST_OVERLAP_def THEN
  RW_ASM_TAC ``EVERY f l`` listTheory.EVERY_MEM THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
  PAT_ASSUM ``f a`` (fn thm => ASSUME_TAC (REWRITE_RULE [(BETA_CONV o concl) thm] thm)) THEN
  RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa q1`` BD_NOT_OVERLAP_BDs_def THEN
  RW_ASM_TAC ``EVERY f l`` listTheory.EVERY_MEM THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``e : bd_pa_type`` thm))) THEN
  PAT_ASSUM ``f a`` (fn thm => ASSUME_TAC (REWRITE_RULE [(BETA_CONV o concl) thm] thm)) THEN
  ASM_REWRITE_TAC []);

val IN_LIST1_IMP_IN_LIST2_def = Define `
  IN_LIST1_IMP_IN_LIST2 (l1 : bd_pa_type list) (l2 : bd_pa_type list) =
  !bd_pa. MEM bd_pa l1 ==> MEM bd_pa l2`;

val IN_EMPTY_LIST_IMP_IN_LIST_lemma = store_thm (
  "IN_EMPTY_LIST_IMP_IN_LIST_lemma",
  ``!l. IN_LIST1_IMP_IN_LIST2 [] l``,
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def, listTheory.MEM]);

val IN_LIST1_IMP_IN_LIST2_REFL_lemma = store_thm (
  "IN_LIST1_IMP_IN_LIST2_REFL_lemma",
  ``!l. IN_LIST1_IMP_IN_LIST2 l l``,
  GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def]);

val MEM_LIST1_IMP_IN_LIST2_lemma = store_thm (
  "MEM_LIST1_IMP_IN_LIST2_lemma",
  ``!bd_pa q.
    MEM bd_pa q
    ==>
    IN_LIST1_IMP_IN_LIST2 [bd_pa] q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MEM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val MEM2_LIST1_IMP_IN_LIST2_lemma = store_thm (
  "MEM2_LIST1_IMP_IN_LIST2_lemma",
  ``!bd_pa1 bd_pa2 q.
    MEM bd_pa1 q /\
    MEM bd_pa2 q
    ==>
    IN_LIST1_IMP_IN_LIST2 [bd_pa1; bd_pa2] q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [listTheory.MEM] THEN
  DISCH_TAC THEN
  Cases_on `bd_pa = bd_pa1` THENL
  [
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``bd_pa <> bd_pa1`` ``P \/ Q`` THEN
   ASM_REWRITE_TAC []
  ]);

val IN_LIST1_AND_IN_LIST1_IMP_IN_LIST2_IMP_IN_LIST2_lemma = store_thm (
  "IN_LIST1_AND_IN_LIST1_IMP_IN_LIST2_IMP_IN_LIST2_lemma",
  ``!bd_pa l1 l2.
    IN_LIST1_IMP_IN_LIST2 l1 l2 /\
    MEM bd_pa l1
    ==>
    MEM bd_pa l2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
  ASM_REWRITE_TAC []);

val IN_LIST1_IMP_IN_LIST2_TRANS_lemma = store_thm (
  "IN_LIST1_IMP_IN_LIST2_TRANS_lemma",
  ``!l1 l2 l3.
    IN_LIST1_IMP_IN_LIST2 l1 l2 /\
    IN_LIST1_IMP_IN_LIST2 l2 l3
    ==>
    IN_LIST1_IMP_IN_LIST2 l1 l3``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!bd_pa. MEM bd_pa l1 ==> MEM bd_pa l2`` (fn thm => ASSUME_TAC (SPEC ``bd_pa : bd_pa_type`` thm)) THEN
  PAT_ASSUM ``!bd_pa. MEM bd_pa l2 ==> MEM bd_pa l3`` (fn thm => ASSUME_TAC (SPEC ``bd_pa : bd_pa_type`` thm)) THEN
  ASM_RW_ASM_TAC ``MEM bd_pa l1`` ``MEM bd_pa l1 ==> MEM bd_pa l2`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa l2`` ``MEM bd_pa l2 ==> MEM bd_pa l3`` THEN
  ASM_REWRITE_TAC []);

val HD_TL_IN_L_IMP_TL_IN_L_lemma = store_thm (
  "HD_TL_IN_L_IMP_TL_IN_L_lemma",
  ``!h t l. IN_LIST1_IMP_IN_LIST2 (h::t) l ==> IN_LIST1_IMP_IN_LIST2 t l``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC (REWRITE_RULE [listTheory.MEM] (SPEC_ALL thm))) THEN
  ASM_REWRITE_TAC []);

val IN_SUFFIX_IMP_IN_LIST_lemma = store_thm (
  "IN_SUFFIX_IMP_IN_LIST_lemma",
  ``!l1 l2. IN_LIST1_IMP_IN_LIST2 l2 (l1 ++ l2)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.MEM_APPEND, boolTheory.OR_INTRO_THM2]);

val BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_BDs_IN_SUBLIST_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_BDs_IN_SUBLIST_lemma",
  ``!bd_pa1 bd_pa2 l1 l2 .
    BD_NOT_OVERLAP_BDs bd_pa1 l2 /\
    IN_LIST1_IMP_IN_LIST2 l1 l2 /\
    MEM bd_pa2 l1
    ==>
    ~BDs_OVERLAP bd_pa1 bd_pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def, IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x. P ==> ~Q`` (fn thm => MATCH_MP_TAC thm) THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_SUBLIST_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_SUBLIST_lemma",
  ``!bd_pa l1 l2.
    BD_NOT_OVERLAP_BDs bd_pa l2 /\
    IN_LIST1_IMP_IN_LIST2 l1 l2
    ==>
    BD_NOT_OVERLAP_BDs bd_pa l1``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC BD_NOT_OVERLAP_BDs_IMP_BD_NOT_OVERLAP_BDs_IN_SUBLIST_lemma THEN
  EXISTS_TAC ``l1 : bd_pa_type list`` THEN
  EXISTS_TAC ``l2 : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val LIST_MEMBER_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_LIST_lemma = store_thm (
  "LIST_MEMBER_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_LIST_lemma",
  ``!l1 l2.
    ~BD_LIST_OVERLAP l2 /\
    IN_LIST1_IMP_IN_LIST2 l1 l2
    ==>
    ~BD_LIST_OVERLAP l1``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x y.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa1 : bd_pa_type``, ``bd_pa2 : bd_pa_type``] thm)) THEN
  ASM_RW_ASM_TAC ``bd_pa1 <> bd_pa2`` ``P ==> Q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``bd_pa1 : bd_pa_type`` thm) THEN ASSUME_TAC (SPEC ``bd_pa2 : bd_pa_type`` thm)) THEN
  ASM_RW_ASM_TAC ``MEM bd_pa1 l1`` ``MEM bd_pa1 l1 ==> MEM bd_pa1 l2`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa2 l1`` ``MEM bd_pa2 l1 ==> MEM bd_pa2 l2`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa1 l2`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa2 l2`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val MEMBERS_OF_NON_OVERLAPPING_LIST_IMP_EQ_OR_NON_OVERLAPPING_BDs_lemma = store_thm (
  "MEMBERS_OF_NON_OVERLAPPING_LIST_IMP_EQ_OR_NON_OVERLAPPING_BDs_lemma",
  ``!bd_pa1 bd_pa2 l.
    ~BD_LIST_OVERLAP l /\
    MEM bd_pa1 l /\
    MEM bd_pa2 l
    ==>
    (bd_pa1 = bd_pa2) \/ ~BDs_OVERLAP bd_pa1 bd_pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa1 : bd_pa_type``, ``bd_pa2 : bd_pa_type``] thm)) THEN
  ASM_RW_ASM_TAC ``MEM bd_pa1 l`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``MEM bd_pa2 l`` ``P ==> Q`` THEN
  Cases_on `bd_pa1 = bd_pa2` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_RW_ASM_TAC ``bd_pa1 <> bd_pa2`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val IN_NON_OVERLAPPING_LIST_IMP_NOT_OVERLAPPING_SUBLIST_OR_IN_SUBLIST_lemma = store_thm (
  "IN_NON_OVERLAPPING_LIST_IMP_NOT_OVERLAPPING_SUBLIST_OR_IN_SUBLIST_lemma",
  ``!l1 l2 bd_pa.
    ¬BD_LIST_OVERLAP l2 /\
    IN_LIST1_IMP_IN_LIST2 l1 l2 /\
    MEM bd_pa l2
    ==>
    BD_NOT_OVERLAP_BDs bd_pa l1 \/ MEM bd_pa l1``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `MEM bd_pa l1` THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def, listTheory.EVERY_MEM] THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  BETA_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``e : bd_pa_type``, ``l1 : bd_pa_type list``, ``l2 : bd_pa_type list``] IN_LIST1_AND_IN_LIST1_IMP_IN_LIST2_IMP_IN_LIST2_lemma)))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_pa : bd_pa_type``, ``e : bd_pa_type``, ``l2 : bd_pa_type list``] MEMBERS_OF_NON_OVERLAPPING_LIST_IMP_EQ_OR_NON_OVERLAPPING_BDs_lemma)))) THEN
  Cases_on `bd_pa = e` THENL
  [
   ASM_RW_ASM_TAC ``bd_pa = e`` ``~MEM bd_pa l1`` THEN
   ASM_RW_ASM_TAC ``MEM e l1`` ``~MEM e l1`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``bd_pa <> e`` ``P \/ Q`` THEN
   ASM_REWRITE_TAC []
  ]);

val BD_IN_CPPI_RAM_BD_QUEUE_IMP_BD_IN_CPPI_RAM_lemma = store_thm (
  "BD_IN_CPPI_RAM_BD_QUEUE_IMP_BD_IN_CPPI_RAM_lemma",
  ``!bd_pa q.
    BDs_IN_CPPI_RAM q /\
    MEM bd_pa q
    ==>
    BD_IN_CPPI_RAM bd_pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_MEM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
  ASM_REWRITE_TAC []);

val IN_LIST1_IMP_IN_LIST2_AND_LIST2_IN_CPPI_RAM_IMP_LIST1_IN_CPPI_RAM_lemma = store_thm (
  "IN_LIST1_IMP_IN_LIST2_AND_LIST2_IN_CPPI_RAM_IMP_LIST1_IN_CPPI_RAM_lemma",
  ``!l1 l2.
    IN_LIST1_IMP_IN_LIST2 l1 l2 /\
    BDs_IN_CPPI_RAM l2
    ==>
    BDs_IN_CPPI_RAM l1``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def, BDs_IN_CPPI_RAM_def, listTheory.EVERY_MEM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!bd_pa. MEM bd_pa l1 ==> MEM bd_pa l2`` (fn thm => ASSUME_TAC (SPEC ``e : bd_pa_type`` thm)) THEN
  ASM_RW_ASM_TAC ``MEM e l1`` ``P ==> Q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``e : bd_pa_type`` thm))) THEN
  ASM_REWRITE_TAC []);

val NO_BD_LIST_OVERLAP_IN_LIST1_IMP_IN_LIST2_IMP_NO_BD_LIST_OVERLAP_lemma = store_thm (
  "NO_BD_LIST_OVERLAP_IN_LIST1_IMP_IN_LIST2_IMP_NO_BD_LIST_OVERLAP_lemma",
  ``!l1 l2 l.
    NO_BD_LIST_OVERLAP l1 l2 /\
    IN_LIST1_IMP_IN_LIST2 l l2
    ==>
    NO_BD_LIST_OVERLAP l1 l``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  REWRITE_TAC [NO_BD_LIST_OVERLAP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!x. MEM x l ==> MEM x l2`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``e : bd_pa_type`` thm))) THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

(* Start of lemmas about independence of two disjoint queues. *)

val EQ_BDs_def = Define `
  EQ_BDs q CPPI_RAM CPPI_RAM' =
  EVERY (\bd_pa. BD_EQ bd_pa CPPI_RAM CPPI_RAM') q`;

val EQ_BDs_SYM_lemma = store_thm (
  "EQ_BDs_SYM_lemma",
  ``!q CPPI_RAM. EQ_BDs q CPPI_RAM CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REWRITE_TAC [BD_EQ_REFL_lemma]);

val EQ_BDs_HD_TL_EQ_BD_EQ_HD_EQ_BDs_TL_lemma = store_thm (
  "EQ_BDs_HD_TL_EQ_BD_EQ_HD_EQ_BDs_TL_lemma",
  ``!h t CPPI_RAM CPPI_RAM'.
    EQ_BDs (h::t) CPPI_RAM CPPI_RAM'
    =
    BD_EQ h CPPI_RAM CPPI_RAM' /\ EQ_BDs t CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EQ_BDs_def, listTheory.EVERY_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC []);

val EQ_BDs_IMP_EQ_SUFFIX_BDs_lemma = store_thm (
  "EQ_BDs_IMP_EQ_SUFFIX_BDs_lemma",
  ``!q1 q2 CPPI_RAM CPPI_RAM'.
    EQ_BDs (q1 ++ q2) CPPI_RAM CPPI_RAM'
    ==>
    EQ_BDs q2 CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_APPEND] THEN
  REWRITE_TAC [boolTheory.AND2_THM]);

val MEM_EQ_BDs_Q_IMP_BD_EQ_lemma = store_thm (
  "MEM_EQ_BDs_Q_IMP_BD_EQ_lemma",
  ``!bd_pa q CPPI_RAM CPPI_RAM'.
    EQ_BDs q CPPI_RAM CPPI_RAM' /\
    MEM bd_pa q
    ==>
    BD_EQ bd_pa CPPI_RAM CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val MEM_EQ_BDs_Q_IMP_READ_NDP_EQ_lemma = store_thm (
  "MEM_EQ_BDs_Q_IMP_READ_NDP_EQ_lemma",
  ``!bd_pa q CPPI_RAM CPPI_RAM'.
    EQ_BDs q CPPI_RAM CPPI_RAM' /\
    MEM bd_pa q
    ==>
    (read_ndp bd_pa CPPI_RAM' = read_ndp bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC BD_EQ_IMP_EQ_NDP_lemma THEN
  MATCH_MP_TAC MEM_EQ_BDs_Q_IMP_BD_EQ_lemma THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

