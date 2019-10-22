open HolKernel Parse boolLib bossLib;
open helperTactics;
open CPPI_RAMTheory;
open bdTheory;
open bd_listTheory;

val _ = new_theory "cppi_ram_writes";

type_abbrev ("cppi_ram_write_step_type", ``: cppi_ram_type -> bd_pa_type -> cppi_ram_type``);

type_abbrev ("cppi_ram_write_step_bd_pas_type", ``: (cppi_ram_write_step_type # bd_pa_type) list``);

(**START OF DEFINITIONS CONCERNING CPPI_RAM_WRITE_STEPS AND SEQUENCES OF CPPI_RAM_WRITE_STEPS**)

val CPPI_RAM_WRITE_STEP_WRITES_BD_def = Define `
  CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step =
  !bd_pa_r bd_pa_w CPPI_RAM.
  BD_IN_CPPI_RAM bd_pa_r /\
  BD_IN_CPPI_RAM bd_pa_w /\
  ~BDs_OVERLAP bd_pa_r bd_pa_w
  ==>
  BD_EQ bd_pa_r CPPI_RAM (cppi_ram_write_step CPPI_RAM bd_pa_w)`;

val CPPI_RAM_WRITE_STEPs_WRITE_BD_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_BD cppi_ram_write_steps =
  EVERY CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_steps`;

val CPPI_RAM_WRITE_STEPs_WRITE_BD_HD_TL_EQ_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_HD_TL_EQ_lemma",
  ``!cppi_ram_write_step cppi_ram_write_steps.
    CPPI_RAM_WRITE_STEPs_WRITE_BD (cppi_ram_write_step::cppi_ram_write_steps) =
    CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD cppi_ram_write_steps``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_def, listTheory.EVERY_DEF]);

val CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def = Define `
  CPPI_RAM_WRITE_STEP_PRESERVES_NDP cppi_ram_write_step =
  !bd_pa CPPI_RAM.
  NDP_UNMODIFIED bd_pa CPPI_RAM (cppi_ram_write_step CPPI_RAM bd_pa)`;

val CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_def = Define `
  CPPI_RAM_WRITE_STEPs_PRESERVE_NDP cppi_ram_write_steps =
  EVERY CPPI_RAM_WRITE_STEP_PRESERVES_NDP cppi_ram_write_steps`;

val CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_HD_TL_EQ_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_HD_TL_EQ_lemma",
  ``!cppi_ram_write_step cppi_ram_write_steps.
    CPPI_RAM_WRITE_STEPs_PRESERVE_NDP (cppi_ram_write_step::cppi_ram_write_steps) =
    CPPI_RAM_WRITE_STEP_PRESERVES_NDP cppi_ram_write_step /\
    CPPI_RAM_WRITE_STEPs_PRESERVE_NDP cppi_ram_write_steps``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_def, listTheory.EVERY_DEF]);

val CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def = Define `
  CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP cppi_ram_write_step =
  CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step /\
  CPPI_RAM_WRITE_STEP_PRESERVES_NDP cppi_ram_write_step`;

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def = Define `
  CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP cppi_ram_write_steps =
  EVERY CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP cppi_ram_write_steps`;

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma",
  ``!cppi_ram_write_step cppi_ram_write_steps.
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (cppi_ram_write_step::cppi_ram_write_steps) =
    CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP cppi_ram_write_step /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP cppi_ram_write_steps``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def, listTheory.EVERY_DEF]);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_EQ_STEPs_WRITE_BD_AND_STEPs_PRESERVE_NDP_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_EQ_STEPs_WRITE_BD_AND_STEPs_PRESERVE_NDP_lemma",
  ``!cppi_ram_write_steps.
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP cppi_ram_write_steps =
    CPPI_RAM_WRITE_STEPs_WRITE_BD cppi_ram_write_steps /\
    CPPI_RAM_WRITE_STEPs_PRESERVE_NDP cppi_ram_write_steps``,
  Induct THENL
  [
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_def, CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_def] THEN
   REWRITE_TAC [listTheory.EVERY_DEF]
   ,
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_HD_TL_EQ_lemma] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_HD_TL_EQ_lemma] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def] THEN
   ASM_REWRITE_TAC [] THEN
   GEN_TAC THEN
   EQ_TAC THEN
   DISCH_TAC THEN
   ASM_REWRITE_TAC []
  ]);

(**END OF DEFINITIONS CONCERNING CPPI_RAM_WRITE_STEPS AND SEQUENCES OF CPPI_RAM_WRITE_STEPS**)



(**START OF DEFINITIONS AND LEMMAS CONCERNING cppi_ram_writes.**)

(*
 * Let
 * cppi_ram_write_step_bd_pas = [(fn, bd_pan), (fn-1, bd_pan-1), ..., (f2, bd_pa2), (f1, bd_pa1)].
 *
 * cppi_ram_write writes CPPI_RAM as:
 * fn (fn-1 ... (f2 (f1 CPPI_RAM bd_pa1) bd_pa2) ... bd_pan-1) bd_pan.
 *)
val reversed_cppi_ram_write_def = Define `
  (reversed_cppi_ram_write
     (CPPI_RAM : cppi_ram_type)
     ([] : cppi_ram_write_step_bd_pas_type)
     =
     CPPI_RAM)
  /\
  (reversed_cppi_ram_write
     CPPI_RAM
     ((reversed_cppi_ram_write_step, reversed_bd_pa)::reversed_cppi_ram_write_step_bd_pas)
   =
   reversed_cppi_ram_write_step
     (reversed_cppi_ram_write CPPI_RAM reversed_cppi_ram_write_step_bd_pas)
     reversed_bd_pa)`;

val reverse_cppi_ram_write_step_bd_pas_with_accumulator_def = Define `
  (reverse_cppi_ram_write_step_bd_pas_with_accumulator
     ([] : cppi_ram_write_step_bd_pas_type)
     reversed_cppi_ram_write_step_bd_pas_accumulator
     =
     reversed_cppi_ram_write_step_bd_pas_accumulator)
  /\
  (reverse_cppi_ram_write_step_bd_pas_with_accumulator
     (cppi_ram_write_step_bd_pa::cppi_ram_write_step_bd_pas)
     reversed_cppi_ram_write_step_bd_pas_accumulator
     =
     reverse_cppi_ram_write_step_bd_pas_with_accumulator
     cppi_ram_write_step_bd_pas
     (cppi_ram_write_step_bd_pa::reversed_cppi_ram_write_step_bd_pas_accumulator))`;

val reverse_cppi_ram_write_step_bd_pas_with_accumulator_EQ_REVERSE_cppi_ram_write_step_bd_pas_APPEND_accumulator_lemma = store_thm (
  "reverse_cppi_ram_write_step_bd_pas_with_accumulator_EQ_REVERSE_cppi_ram_write_step_bd_pas_APPEND_accumulator_lemma",
  ``!l a.
    reverse_cppi_ram_write_step_bd_pas_with_accumulator l a = (REVERSE l) ++ a``,
  Induct_on `l` THENL
  [
   GEN_TAC THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
   REWRITE_TAC [listTheory.REVERSE_DEF] THEN
   REWRITE_TAC [listTheory.APPEND]
   ,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
   PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (SPEC ``h::a : cppi_ram_write_step_bd_pas_type`` thm)) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [listTheory.REVERSE_DEF, GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
  ]);

val reverse_cppi_ram_write_step_bd_pas_def = Define `
  reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas =
  reverse_cppi_ram_write_step_bd_pas_with_accumulator cppi_ram_write_step_bd_pas []`;

val reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma = store_thm (
  "reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma",
  ``!cppi_ram_write_step_bd_pas.
  reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas =
  REVERSE cppi_ram_write_step_bd_pas``,
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_EQ_REVERSE_cppi_ram_write_step_bd_pas_APPEND_accumulator_lemma] THEN
  REWRITE_TAC [listTheory.APPEND_NIL]);

val reverse_cppi_ram_write_step_bd_pas_CONS_EQ_LAST_lemma = store_thm (
  "reverse_cppi_ram_write_step_bd_pas_CONS_EQ_LAST_lemma",
  ``!cppi_ram_write_step bd_pa cppi_ram_write_step_bd_pas.
    reverse_cppi_ram_write_step_bd_pas ((cppi_ram_write_step, bd_pa)::cppi_ram_write_step_bd_pas) =
    reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas ++ [(cppi_ram_write_step, bd_pa)]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  ONCE_REWRITE_TAC [SYM (REWRITE_RULE [CONJUNCT1 listTheory.APPEND] (SPECL [``[] : cppi_ram_write_step_bd_pas_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``, ``(cppi_ram_write_step : cppi_ram_write_step_type, bd_pa: bd_pa_type)``] (INST_TYPE [``: 'a`` |-> ``: cppi_ram_write_step_type # bd_pa_type``] (CONJUNCT2 listTheory.APPEND))))] THEN
  REWRITE_TAC [listTheory.REVERSE_APPEND] THEN
  REWRITE_TAC [listTheory.APPEND_NIL, listTheory.REVERSE_DEF, listTheory.APPEND]);
  
val TWICE_reverse_cppi_ram_write_step_bd_pas_EQ_lemma = store_thm (
  "TWICE_reverse_cppi_ram_write_step_bd_pas_EQ_lemma",
  ``!cppi_ram_write_step_bd_pas.
    reverse_cppi_ram_write_step_bd_pas (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas) = cppi_ram_write_step_bd_pas``,
  GEN_TAC THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_EQ_REVERSE_cppi_ram_write_step_bd_pas_APPEND_accumulator_lemma] THEN
  REWRITE_TAC [listTheory.APPEND_NIL, listTheory.REVERSE_REVERSE]);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_EQ_reverse_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_EQ_reverse_cppi_ram_write_step_bd_pas_lemma",
  ``!cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type.
    CPPI_RAM_WRITE_STEPs_WRITE_BD (MAP FST (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)) =
    CPPI_RAM_WRITE_STEPs_WRITE_BD (MAP FST cppi_ram_write_step_bd_pas)``,
  GEN_TAC THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM, listTheory.MEM_MAP, listTheory.MEM_REVERSE]);

val CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_EQ_reverse_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_EQ_reverse_cppi_ram_write_step_bd_pas_lemma",
  ``!cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type.
    CPPI_RAM_WRITE_STEPs_PRESERVE_NDP (MAP FST (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)) =
    CPPI_RAM_WRITE_STEPs_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)``,
  GEN_TAC THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM, listTheory.MEM_MAP, listTheory.MEM_REVERSE]);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_EQ_reverse_cppi_ram_write_step_bd_pas_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_EQ_reverse_cppi_ram_write_step_bd_pas_lemma",
  ``!cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type.
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)) =
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)``,
  GEN_TAC THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM, listTheory.MEM_MAP, listTheory.MEM_REVERSE]);




(*
 * Let
 * cppi_ram_write_step_bd_pas = [(f1, bd_pa1), (f2, bd_pa2), ..., (f2, bd_pan-1), (f1, bd_pan)].
 *
 * cppi_ram_write writes CPPI_RAM as:
 * f1 (f2 ... (fn-1 (fn CPPI_RAM bd_pan) bd_pan-1) ... bd_pa2) bd_pa1.
 *)
val cppi_ram_write_def = Define `
  cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas =
  reversed_cppi_ram_write CPPI_RAM (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)`;

val cppi_ram_write_EMPTY_EQ_ID_lemma = store_thm (
  "cppi_ram_write_EMPTY_EQ_ID_lemma",
  ``!CPPI_RAM. cppi_ram_write CPPI_RAM [] = CPPI_RAM``,
  GEN_TAC THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
  REWRITE_TAC [reversed_cppi_ram_write_def]);

val reversed_cppi_ram_write_EQ_START_WRITE_LAST_lemma = store_thm (
  "reversed_cppi_ram_write_EQ_START_WRITE_LAST_lemma",
  ``!CPPI_RAM cppi_ram_write_step bd_pa reversed_cppi_ram_write_step_bd_pas.
    reversed_cppi_ram_write
      CPPI_RAM
      (reversed_cppi_ram_write_step_bd_pas ++ [(cppi_ram_write_step, bd_pa)])
    =
    reversed_cppi_ram_write
      (cppi_ram_write_step CPPI_RAM bd_pa)
      (reversed_cppi_ram_write_step_bd_pas)``,
  Induct_on `reversed_cppi_ram_write_step_bd_pas` THENL
  [
   REWRITE_TAC [rich_listTheory.APPEND_NIL] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def]
   ,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.APPEND] THEN
   Cases_on `h` THEN
   REWRITE_TAC [reversed_cppi_ram_write_def] THEN
   PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (SPECL [``CPPI_RAM : cppi_ram_type``, ``cppi_ram_write_step : cppi_ram_write_step_type``, ``bd_pa : bd_pa_type``] thm)) THEN
   ASM_REWRITE_TAC []
  ]);

val reversed_cppi_ram_write_EQ_START_WRITE_TAIL_lemma = store_thm (
  "reversed_cppi_ram_write_EQ_START_WRITE_TAIL_lemma",
  ``!CPPI_RAM reversed_cppi_ram_write_step_bd_pas1 reversed_cppi_ram_write_step_bd_pas2.
    reversed_cppi_ram_write
      CPPI_RAM
      (reversed_cppi_ram_write_step_bd_pas1 ++ reversed_cppi_ram_write_step_bd_pas2)
    =
    reversed_cppi_ram_write
      (reversed_cppi_ram_write CPPI_RAM reversed_cppi_ram_write_step_bd_pas2)
      reversed_cppi_ram_write_step_bd_pas1``,
  Induct_on `reversed_cppi_ram_write_step_bd_pas2` THENL
  [
   REWRITE_TAC [listTheory.APPEND_NIL] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def]
   ,
   REPEAT GEN_TAC THEN
   Cases_on `h` THEN
   PAT_ASSUM ``P`` (fn thm => ASSUME_TAC (SPECL [``CPPI_RAM : cppi_ram_type``, ``reversed_cppi_ram_write_step_bd_pas1 ++ [(q,r)] : cppi_ram_write_step_bd_pas_type``] thm)) THEN
   RW_ASM_TAC ``P`` (GSYM listTheory.APPEND_ASSOC) THEN
   RW_ASM_TAC ``P`` (listTheory.APPEND) THEN
   ASM_REWRITE_TAC [] THEN
   WEAKEN_TAC (fn thm => true) THEN
   REWRITE_TAC [reversed_cppi_ram_write_EQ_START_WRITE_LAST_lemma] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def]
  ]);

val reversed_reversed_cppi_ram_write_EQ_reversed_FIRST_reversed_lemma = store_thm (
  "reversed_reversed_cppi_ram_write_EQ_reversed_FIRST_reversed_lemma",
  ``!CPPI_RAM cppi_ram_write_step bd_pa cppi_ram_write_step_bd_pas.
    reversed_cppi_ram_write
      CPPI_RAM
      (reverse_cppi_ram_write_step_bd_pas ((cppi_ram_write_step, bd_pa)::cppi_ram_write_step_bd_pas))
    =
    reversed_cppi_ram_write
      (cppi_ram_write_step CPPI_RAM bd_pa)
      (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM reversed_cppi_ram_write_EQ_START_WRITE_LAST_lemma] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_CONS_EQ_LAST_lemma]);

val cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma = store_thm (
  "cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma",
  ``!cppi_ram_write_step bd_pa_w cppi_ram_write_step_bd_pas CPPI_RAM.
    cppi_ram_write CPPI_RAM ((cppi_ram_write_step, bd_pa_w)::cppi_ram_write_step_bd_pas) =
    cppi_ram_write (cppi_ram_write_step CPPI_RAM bd_pa_w) cppi_ram_write_step_bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [reversed_reversed_cppi_ram_write_EQ_reversed_FIRST_reversed_lemma]);

val cppi_ram_write1_EQ_REVERSE_lemma = store_thm (
  "cppi_ram_write1_EQ_REVERSE_lemma",
  ``!CPPI_RAM cppi_ram_write_step_bd_pa.
    cppi_ram_write CPPI_RAM [cppi_ram_write_step_bd_pa] =
    reversed_cppi_ram_write CPPI_RAM [cppi_ram_write_step_bd_pa]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def]);

val cppi_ram_write2_EQ_REVERSE_lemma = store_thm (
  "cppi_ram_write2_EQ_REVERSE_lemma",
  ``!CPPI_RAM cppi_ram_write_step_bd_pa1 cppi_ram_write_step_bd_pa2.
    cppi_ram_write CPPI_RAM [cppi_ram_write_step_bd_pa1; cppi_ram_write_step_bd_pa2] =
    reversed_cppi_ram_write CPPI_RAM [cppi_ram_write_step_bd_pa2; cppi_ram_write_step_bd_pa1]``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def]);

val cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma = store_thm (
  "cppi_ram_write_ONE_STEP_EQ_cppi_ram_write_ONE_STEP_lemma",
  ``!CPPI_RAM cppi_ram_write_step bd_pa.
    cppi_ram_write CPPI_RAM [(cppi_ram_write_step, bd_pa)] =
    cppi_ram_write_step CPPI_RAM bd_pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
  REWRITE_TAC [reversed_cppi_ram_write_def]);

val cppi_ram_write_TWO_STEPS_EQ_cppi_ram_write_TWO_STEPS_lemma = store_thm (
  "cppi_ram_write_TWO_STEPS_EQ_cppi_ram_write_TWO_STEPS_lemma",
  ``!CPPI_RAM cppi_ram_write_step1 bd_pa1 cppi_ram_write_step2 bd_pa2.
    cppi_ram_write CPPI_RAM [(cppi_ram_write_step1, bd_pa1); (cppi_ram_write_step2, bd_pa2)] =
    cppi_ram_write_step2 (cppi_ram_write_step1 CPPI_RAM bd_pa1) bd_pa2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
  REWRITE_TAC [reversed_cppi_ram_write_def]);









val REVERSED_CPPI_RAM_WRITE_WRITES_BDs_def = Define `
  REVERSED_CPPI_RAM_WRITE_WRITES_BDs reversed_cppi_ram_write_step_bd_pas =
  !bd_pa_r CPPI_RAM.
  BD_IN_CPPI_RAM bd_pa_r /\
  BDs_IN_CPPI_RAM (MAP SND reversed_cppi_ram_write_step_bd_pas) /\
  BD_NOT_OVERLAP_BDs bd_pa_r (MAP SND reversed_cppi_ram_write_step_bd_pas)
  ==>
  BD_EQ bd_pa_r CPPI_RAM (reversed_cppi_ram_write CPPI_RAM reversed_cppi_ram_write_step_bd_pas)`;

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def = Define `
  REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA reversed_cppi_ram_write_step_bd_pas bd_pa =
  !CPPI_RAM. NDP_UNMODIFIED bd_pa CPPI_RAM (reversed_cppi_ram_write CPPI_RAM reversed_cppi_ram_write_step_bd_pas)`;

val CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def = Define `
  CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa =
  !CPPI_RAM. NDP_UNMODIFIED bd_pa CPPI_RAM (cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)`;

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_EQ_UNREVERSED_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_EQ_UNREVERSED_lemma",
  ``!cppi_ram_write_step_bd_pas bd_pa.
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas) bd_pa
    =
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  REWRITE_TAC [cppi_ram_write_def]);

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_def = Define `
  REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs
  reversed_cppi_ram_write_step_bd_pas
  bd_pas
  =
  EVERY
  (REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA reversed_cppi_ram_write_step_bd_pas)
  bd_pas`;

val CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_def = Define `
  CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs cppi_ram_write_step_bd_pas bd_pas
  =
  EVERY (CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas) bd_pas`;

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_EQ_UNREVERSED_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_EQ_UNREVERSED_lemma",
  ``!cppi_ram_write_step_bd_pas bd_pas.
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs
    (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)
    bd_pas
    =
    CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs cppi_ram_write_step_bd_pas bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_EQ_UNREVERSED_lemma]);

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_HD_TL_EQ_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_HD_TL_EQ_lemma",
  ``!cppi_ram_write_step_bd_pas bd_pa bd_pas.
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs cppi_ram_write_step_bd_pas (bd_pa::bd_pas) =
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa /\
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs cppi_ram_write_step_bd_pas bd_pas``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_def, listTheory.EVERY_DEF]);

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_def = Define `
  REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs reversed_cppi_ram_write_step_bd_pas =
  REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs reversed_cppi_ram_write_step_bd_pas (MAP SND reversed_cppi_ram_write_step_bd_pas)`;

val CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_def = Define `
  CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs cppi_ram_write_step_bd_pas =
  CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs cppi_ram_write_step_bd_pas (MAP SND cppi_ram_write_step_bd_pas)`;

val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_EQ_UNREVERSED_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_EQ_UNREVERSED_lemma",
  ``!cppi_ram_write_step_bd_pas.
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)
    =
    CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs cppi_ram_write_step_bd_pas``,
  GEN_TAC THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_def] THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_EQ_UNREVERSED_lemma] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDPs_OF_BDs_AT_BD_PAs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  REWRITE_TAC [listTheory.MEM_MAP] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  REWRITE_TAC [listTheory.MEM_REVERSE]);

val REVERSED_CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs_def = Define `
  REVERSED_CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs reversed_cppi_ram_write_step_bd_pas =
  REVERSED_CPPI_RAM_WRITE_WRITES_BDs reversed_cppi_ram_write_step_bd_pas /\
  REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs reversed_cppi_ram_write_step_bd_pas`;

val CPPI_RAM_WRITE_WRITES_BDs_def = Define `
  CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas =
  !bd_pa_r CPPI_RAM.
  BD_IN_CPPI_RAM bd_pa_r /\
  BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas) /\
  BD_NOT_OVERLAP_BDs bd_pa_r (MAP SND cppi_ram_write_step_bd_pas)
  ==>
  BD_EQ bd_pa_r CPPI_RAM (cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas)`;

val CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs_def = Define `
  CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs cppi_ram_write_step_bd_pas =
  CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas /\
  CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs cppi_ram_write_step_bd_pas`;

val BDs_IN_CPPI_RAM_MAP_SND_EQ_MAP_SND_REVERSED_lemma = store_thm (
  "BDs_IN_CPPI_RAM_MAP_SND_EQ_MAP_SND_REVERSED_lemma",
  ``!cppi_ram_write_step_bd_pas.
    BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas) =
    BDs_IN_CPPI_RAM (MAP SND (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas))``,
  GEN_TAC THEN
  REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_MEM, listTheory.MEM_MAP] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  REWRITE_TAC [listTheory.MEM_REVERSE]);

val BD_NOT_OVERLAP_BDs_MAP_SND_EQ_MAP_SND_REVERSED_lemma = store_thm (
  "BD_NOT_OVERLAP_BDs_MAP_SND_EQ_MAP_SND_REVERSED_lemma",
  ``!bd_pa cppi_ram_write_step_bd_pas.
    BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas) =
    BD_NOT_OVERLAP_BDs bd_pa (MAP SND (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas))``,
  GEN_TAC THEN
  REWRITE_TAC [BD_NOT_OVERLAP_BDs_def, listTheory.EVERY_MEM, listTheory.MEM_MAP] THEN
  REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_EQ_REVERSE_lemma] THEN
  REWRITE_TAC [listTheory.MEM_REVERSE]);

val REVERSED_CPPI_RAM_WRITE_WRITES_BDs_EQ_CPPI_RAM_WRITE_WRITES_BDs_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_WRITES_BDs_EQ_CPPI_RAM_WRITE_WRITES_BDs_lemma",
  ``!cppi_ram_write_step_bd_pas.
    REVERSED_CPPI_RAM_WRITE_WRITES_BDs
    (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)
    =
    CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas``,
  GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_WRITES_BDs_def] THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_WRITES_BDs_def] THEN
  REWRITE_TAC [cppi_ram_write_def] THEN
  REWRITE_TAC [GSYM BDs_IN_CPPI_RAM_MAP_SND_EQ_MAP_SND_REVERSED_lemma] THEN
  REWRITE_TAC [GSYM BD_NOT_OVERLAP_BDs_MAP_SND_EQ_MAP_SND_REVERSED_lemma]);

val REVERSED_CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs_EQ_UNREVERSED_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs_EQ_UNREVERSED_lemma",
  ``!cppi_ram_write_step_bd_pas.
  REVERSED_CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs (reverse_cppi_ram_write_step_bd_pas cppi_ram_write_step_bd_pas)
  =
  CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs cppi_ram_write_step_bd_pas``,
  GEN_TAC THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_WRITES_BDs_AND_PRESERVES_NDPs_def] THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_WRITES_BDs_EQ_CPPI_RAM_WRITE_WRITES_BDs_lemma] THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDPs_OF_WRITTEN_BDs_EQ_UNREVERSED_lemma]);

(**END OF DEFINITIONS AND LEMMAS CONCERNING cppi_ram_writes.**)











val NON_OVERLAPPING_BDs_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_REVERSED_PRESERVES_NDP_IMP_REVERSED_STEP_PRESERVES_NDP_lemma = store_thm (
  "NON_OVERLAPPING_BDs_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_REVERSED_PRESERVES_NDP_IMP_REVERSED_STEP_PRESERVES_NDP_lemma",
  ``!bd_pa_r bd_pa_w cppi_ram_write_step reversed_cppi_ram_write_step_bd_pas.
    BD_IN_CPPI_RAM bd_pa_r /\
    BD_IN_CPPI_RAM bd_pa_w /\
    ~BDs_OVERLAP bd_pa_r bd_pa_w /\
    CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step /\
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA reversed_cppi_ram_write_step_bd_pas bd_pa_r
    ==>
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA ((cppi_ram_write_step, bd_pa_w)::reversed_cppi_ram_write_step_bd_pas) bd_pa_r``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_def] THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [reversed_cppi_ram_write_def] THEN
  PAT_ASSUM ``!x y. P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_r : bd_pa_type``, ``bd_pa_w : bd_pa_type``, ``reversed_cppi_ram_write CPPI_RAM reversed_cppi_ram_write_step_bd_pas``] thm)) THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_w`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa_r bd_pa_w`` ``P ==> Q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  MATCH_MP_TAC BD_EQ_AND_NDP_UNMODIFIED_IMP_NDP_UNMODIFIED_lemma THEN
  EXISTS_TAC ``reversed_cppi_ram_write CPPI_RAM reversed_cppi_ram_write_step_bd_pas`` THEN
  ASM_REWRITE_TAC []);

val NON_OVERLAPPING_BDs_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_IMP_STEP_PRESERVES_NDP_lemma = store_thm (
  "NON_OVERLAPPING_BDs_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_IMP_STEP_PRESERVES_NDP_lemma",
  ``!bd_pa_r bd_pa_w cppi_ram_write_step cppi_ram_write_step_bd_pas.
    BD_IN_CPPI_RAM bd_pa_r /\
    BD_IN_CPPI_RAM bd_pa_w /\
    ~BDs_OVERLAP bd_pa_r bd_pa_w /\
    CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step /\
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa_r
    ==>
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA ((cppi_ram_write_step, bd_pa_w)::cppi_ram_write_step_bd_pas) bd_pa_r``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_WRITES_BD_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x y z. P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_r : bd_pa_type``, ``bd_pa_w : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_w`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa_r bd_pa_w`` ``P ==> Q`` THEN
  PAT_ASSUM ``!x. P`` (fn thm => ASSUME_TAC (SPEC ``(cppi_ram_write_step : cppi_ram_write_step_type) CPPI_RAM bd_pa_w`` thm)) THEN
  RW_ASM_TAC ``NDP_UNMODIFIED a m1 m2`` (GSYM cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma) THEN
  MATCH_MP_TAC BD_EQ_NDP_UNMODIFIED_TRANS_UNMODIFIED_lemma THEN
  EXISTS_TAC ``(cppi_ram_write_step : cppi_ram_write_step_type) CPPI_RAM bd_pa_w`` THEN
  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_IMP_REVERSED_CPPI_RAM_WRITE_WRITES_BDs_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_IMP_REVERSED_CPPI_RAM_WRITE_WRITES_BDs_lemma",
  ``!cppi_ram_write_step_bd_pas.
    CPPI_RAM_WRITE_STEPs_WRITE_BD (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    REVERSED_CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas``,
  Induct THENL
  [
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_WRITES_BDs_def, CPPI_RAM_WRITE_STEPs_WRITE_BD_def] THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [BDs_IN_CPPI_RAM_def, BD_NOT_OVERLAP_BDs_def] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def] THEN
   REWRITE_TAC [listTheory.EVERY_DEF] THEN
   REWRITE_TAC [BD_EQ_def]
   ,
   Cases_on `h` THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_HD_TL_EQ_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD (MAP FST cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_WRITES_BDs_def] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [BDs_IN_CPPI_RAM_HD_TL_EQ_lemma, BD_NOT_OVERLAP_BDs_HD_TL_EQ_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   REWRITE_TAC [reversed_cppi_ram_write_def] THEN
   RW_ASM_TAC ``REVERSED_CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas`` REVERSED_CPPI_RAM_WRITE_WRITES_BDs_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_r : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
   KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa_r (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD q`` CPPI_RAM_WRITE_STEP_WRITES_BD_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_r : bd_pa_type``, ``r : bd_pa_type``, ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas``] thm)) THEN
   ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM r`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa_r r`` ``P ==> Q`` THEN
   MATCH_MP_TAC BD_EQ_TRANS_lemma THEN
   EXISTS_TAC ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas`` THEN
   ASM_REWRITE_TAC []
  ]);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_IMP_CPPI_RAM_WRITE_WRITES_BDs_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_IMP_CPPI_RAM_WRITE_WRITES_BDs_lemma",
  ``!cppi_ram_write_step_bd_pas.
    CPPI_RAM_WRITE_STEPs_WRITE_BD (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas``,
  Induct THENL
  [
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_WRITES_BDs_def, CPPI_RAM_WRITE_STEPs_WRITE_BD_def] THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [BDs_IN_CPPI_RAM_def, BD_NOT_OVERLAP_BDs_def] THEN
   REWRITE_TAC [cppi_ram_write_def] THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def] THEN
   REWRITE_TAC [BD_EQ_def]
   ,
   Cases_on `h` THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_HD_TL_EQ_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD (MAP FST cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   REWRITE_TAC [CPPI_RAM_WRITE_WRITES_BDs_def] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [BDs_IN_CPPI_RAM_HD_TL_EQ_lemma, BD_NOT_OVERLAP_BDs_HD_TL_EQ_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_WRITES_BDs cppi_ram_write_step_bd_pas`` CPPI_RAM_WRITE_WRITES_BDs_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_r : bd_pa_type``, ``(q : cppi_ram_write_step_type) CPPI_RAM r``] thm)) THEN
   KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa_r (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD q`` CPPI_RAM_WRITE_STEP_WRITES_BD_def THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa_r : bd_pa_type``, ``r : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
   ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa_r`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM r`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa_r r`` ``P ==> Q`` THEN
   REWRITE_TAC [cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma] THEN
   MATCH_MP_TAC BD_EQ_TRANS_lemma THEN
   EXISTS_TAC ``(q : cppi_ram_write_step_type) CPPI_RAM r`` THEN
   ASM_REWRITE_TAC []
  ]);



val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_REVERSED_PRESERVES_NON_OVERLAPPING_BD_PA_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_REVERSED_PRESERVES_NON_OVERLAPPING_BD_PA_lemma",
  ``!bd_pa cppi_ram_write_step_bd_pas.
    BD_IN_CPPI_RAM bd_pa /\
    BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas) /\
    ~BD_LIST_OVERLAP (bd_pa::MAP SND cppi_ram_write_step_bd_pas) /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  Induct_on `cppi_ram_write_step_bd_pas` THENL
  [
   REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def, NDP_UNMODIFIED_def]
   ,
   Cases_on `h` THEN
   GEN_TAC THEN
   REWRITE_TAC [listTheory.MAP] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
   GEN_TAC THEN
   REWRITE_TAC [reversed_cppi_ram_write_def] THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``bd_pa : bd_pa_type`` thm)) THEN
   PAT_ASSUM ``~BD_LIST_OVERLAP (bd_pa::r::MAP SND cppi_ram_write_step_bd_pas)`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BD_LIST_HDs_EQ_lemma] thm)) THEN
   ASSUME_TAC (UNDISCH (SPECL [``r : bd_pa_type``, ``bd_pa::MAP SND (cppi_ram_write_step_bd_pas : (cppi_ram_write_step_type # bd_pa_type) list)``] NO_OVERLAP_IMP_NO_OVERLAP_TAIL_lemma)) THEN
   KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
   RW_ASM_TAC ``BDs_IN_CPPI_RAM (r::MAP SND cppi_ram_write_step_bd_pas)`` BDs_IN_CPPI_RAM_HD_TL_EQ_lemma THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``~BD_LIST_OVERLAP (h::t)`` ``P ==> Q`` THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (q::MAP FST cppi_ram_write_step_bd_pas)`` CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   RW_ASM_TAC ``~BD_LIST_OVERLAP l`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (REWRITE_RULE [listTheory.MEM] (SPECL [``r : bd_pa_type``, ``bd_pa : bd_pa_type``] thm))) THEN
   Cases_on `bd_pa = r` THENL
   [
    ASM_REWRITE_TAC [] THEN
    ASM_RW_ASM_TAC ``bd_pa = r`` ``REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa`` THEN
    RW_ASM_TAC ``REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas r`` REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def THEN
    PAT_ASSUM ``!x y.P`` (fn thm => ASSUME_TAC (SPECL [``r : bd_pa_type``, ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas``] thm)) THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``CPPI_RAM : cppi_ram_type`` thm)) THEN
    MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
    EXISTS_TAC ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas`` THEN
    ASM_REWRITE_TAC []
    ,
    REFLECT_ASM_TAC ``bd_pa <> r`` THEN
    ASM_RW_ASM_TAC ``r <> bd_pa`` ``P ==> Q`` THEN
    RW_ASM_TAC ``REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa`` REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``CPPI_RAM : cppi_ram_type`` thm)) THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD q`` CPPI_RAM_WRITE_STEP_WRITES_BD_def THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa : bd_pa_type``, ``r : bd_pa_type``, ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas``] thm)) THEN
    ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
    ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM r`` ``P ==> Q`` THEN
    PAT_ASSUM ``~BDs_OVERLAP r bd_pa`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] thm)) THEN
    ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa r`` ``P ==> Q`` THEN
    PAT_ASSUM ``BD_EQ a m1 m2`` (fn thm => ASSUME_TAC (MATCH_MP BD_EQ_IMP_NDP_UNMODIFIED_lemma thm)) THEN
    MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
    EXISTS_TAC ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas`` THEN
    ASM_REWRITE_TAC []
   ]
  ]);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_PRESERVES_NON_OVERLAPPING_BD_PA_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_PRESERVES_NON_OVERLAPPING_BD_PA_lemma",
  ``!bd_pa cppi_ram_write_step_bd_pas.
    BD_IN_CPPI_RAM bd_pa /\
    BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas) /\
    ~BD_LIST_OVERLAP (bd_pa::MAP SND cppi_ram_write_step_bd_pas) /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  Induct_on `cppi_ram_write_step_bd_pas` THENL
  [
   REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
   REWRITE_TAC [cppi_ram_write_def, NDP_UNMODIFIED_def] THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def]
   ,
   Cases_on `h` THEN
   GEN_TAC THEN
   REWRITE_TAC [listTheory.MAP] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
   GEN_TAC THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
   PAT_ASSUM ``~BD_LIST_OVERLAP (bd_pa::r::MAP SND cppi_ram_write_step_bd_pas)`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BD_LIST_HDs_EQ_lemma] thm)) THEN
   ASSUME_TAC (UNDISCH (SPECL [``r : bd_pa_type``, ``bd_pa::MAP SND (cppi_ram_write_step_bd_pas : (cppi_ram_write_step_type # bd_pa_type) list)``] NO_OVERLAP_IMP_NO_OVERLAP_TAIL_lemma)) THEN
   KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
   RW_ASM_TAC ``BDs_IN_CPPI_RAM (r::MAP SND cppi_ram_write_step_bd_pas)`` BDs_IN_CPPI_RAM_HD_TL_EQ_lemma THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``~BD_LIST_OVERLAP (h::t)`` ``P ==> Q`` THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (q::MAP FST cppi_ram_write_step_bd_pas)`` CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   RW_ASM_TAC ``~BD_LIST_OVERLAP l`` NOT_BD_LIST_OVERLAP_EQ_ALL_DISTINCT_MEMBERS_NOT_OVERLAP_lemma THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (REWRITE_RULE [listTheory.MEM] (SPECL [``r : bd_pa_type``, ``bd_pa : bd_pa_type``] thm))) THEN
   Cases_on `bd_pa = r` THENL
   [
    ASM_REWRITE_TAC [] THEN
    ASM_RW_ASM_TAC ``bd_pa = r`` ``CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa`` THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas r`` CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def THEN
    PAT_ASSUM ``!x y.P`` (fn thm => ASSUME_TAC (SPECL [``r : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``(q : cppi_ram_write_step_type) CPPI_RAM r`` thm)) THEN
    REWRITE_TAC [cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma] THEN
    MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
    EXISTS_TAC ``(q : cppi_ram_write_step_type) CPPI_RAM r`` THEN
    ASM_REWRITE_TAC []
    ,
    REFLECT_ASM_TAC ``bd_pa <> r`` THEN
    ASM_RW_ASM_TAC ``r <> bd_pa`` ``P ==> Q`` THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa`` CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``(q : cppi_ram_write_step_type) CPPI_RAM r`` thm)) THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD q`` CPPI_RAM_WRITE_STEP_WRITES_BD_def THEN
    PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa : bd_pa_type``, ``r : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
    ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
    ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM r`` ``P ==> Q`` THEN
    PAT_ASSUM ``~BDs_OVERLAP r bd_pa`` (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [BDs_OVERLAP_SYM_lemma] thm)) THEN
    ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa r`` ``P ==> Q`` THEN
    PAT_ASSUM ``BD_EQ a m1 m2`` (fn thm => ASSUME_TAC (MATCH_MP BD_EQ_IMP_NDP_UNMODIFIED_lemma thm)) THEN
    MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
    EXISTS_TAC ``(q : cppi_ram_write_step_type) CPPI_RAM r`` THEN
    ASM_REWRITE_TAC [cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma]
   ]
  ]);



val CPPI_RAM_WRITE_STEP_AND_REVERSED_PRESERVE_NDP_AT_BD_PA_lemma = store_thm (
  "CPPI_RAM_WRITE_STEP_AND_REVERSED_PRESERVE_NDP_AT_BD_PA_lemma",
  ``!bd_pa cppi_ram_write_step cppi_ram_write_step_bd_pas.
    CPPI_RAM_WRITE_STEP_PRESERVES_NDP cppi_ram_write_step /\
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa
    ==>
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA ((cppi_ram_write_step, bd_pa)::cppi_ram_write_step_bd_pas) bd_pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [reversed_cppi_ram_write_def] THEN
  PAT_ASSUM ``!x. NDP_UNMODIFIED a m1 m2`` (fn thm => ASSUME_TAC (SPECL [``CPPI_RAM : cppi_ram_type``] thm)) THEN
  PAT_ASSUM ``!x y.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa : bd_pa_type``, ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas``] thm)) THEN
  MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
  EXISTS_TAC ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas`` THEN
  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_STEP_AND_PRESERVE_NDP_AT_BD_PA_lemma = store_thm (
  "CPPI_RAM_WRITE_STEP_AND_PRESERVE_NDP_AT_BD_PA_lemma",
  ``!bd_pa cppi_ram_write_step cppi_ram_write_step_bd_pas.
    CPPI_RAM_WRITE_STEP_PRESERVES_NDP cppi_ram_write_step /\
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa
    ==>
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA ((cppi_ram_write_step, bd_pa)::cppi_ram_write_step_bd_pas) bd_pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEP_PRESERVES_NDP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  GEN_TAC THEN
  PAT_ASSUM ``!x. NDP_UNMODIFIED a m1 m2`` (fn thm => ASSUME_TAC (SPECL [``(cppi_ram_write_step : cppi_ram_write_step_type) CPPI_RAM bd_pa``] thm)) THEN
  PAT_ASSUM ``!x y.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
  REWRITE_TAC [cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma] THEN
  MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
  EXISTS_TAC ``(cppi_ram_write_step : cppi_ram_write_step_type) CPPI_RAM bd_pa`` THEN
  ASM_REWRITE_TAC []);



val REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_AND_STEP_WRITES_NON_OVERLAPPING_BD_IMP_NDP_PRESERVED_lemma = store_thm (
  "REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_AND_STEP_WRITES_NON_OVERLAPPING_BD_IMP_NDP_PRESERVED_lemma",
  ``!bd_pa1 bd_pa2 cppi_ram_write_step cppi_ram_write_step_bd_pas.
    BD_IN_CPPI_RAM bd_pa1 /\
    BD_IN_CPPI_RAM bd_pa2 /\
    ~BDs_OVERLAP bd_pa1 bd_pa2 /\
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa1 /\
    CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step
    ==>
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA ((cppi_ram_write_step, bd_pa2)::cppi_ram_write_step_bd_pas) bd_pa1``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  GEN_TAC THEN
  REWRITE_TAC [reversed_cppi_ram_write_def] THEN
  RW_ASM_TAC ``REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa1`` REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step`` CPPI_RAM_WRITE_STEP_WRITES_BD_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa1 : bd_pa_type``, ``bd_pa2 : bd_pa_type``, ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas``] thm)) THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa1`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa2`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa1 bd_pa2`` ``P ==> Q`` THEN
  PAT_ASSUM ``BD_EQ a m1 m2`` (fn thm => ASSUME_TAC (MATCH_MP BD_EQ_IMP_NDP_UNMODIFIED_lemma thm)) THEN
  MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
  EXISTS_TAC ``reversed_cppi_ram_write CPPI_RAM cppi_ram_write_step_bd_pas`` THEN
  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_PRESERVES_NDP_AND_STEP_WRITES_NON_OVERLAPPING_BD_IMP_NDP_PRESERVED_lemma = store_thm (
  "CPPI_RAM_WRITE_PRESERVES_NDP_AND_STEP_WRITES_NON_OVERLAPPING_BD_IMP_NDP_PRESERVED_lemma",
  ``!bd_pa1 bd_pa2 cppi_ram_write_step cppi_ram_write_step_bd_pas.
    BD_IN_CPPI_RAM bd_pa1 /\
    BD_IN_CPPI_RAM bd_pa2 /\
    ~BDs_OVERLAP bd_pa1 bd_pa2 /\
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa1 /\
    CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step
    ==>
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA ((cppi_ram_write_step, bd_pa2)::cppi_ram_write_step_bd_pas) bd_pa1``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
  GEN_TAC THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa1`` CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``(cppi_ram_write_step : cppi_ram_write_step_type) CPPI_RAM bd_pa2`` thm)) THEN
  RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD cppi_ram_write_step`` CPPI_RAM_WRITE_STEP_WRITES_BD_def THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPECL [``bd_pa1 : bd_pa_type``, ``bd_pa2 : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``] thm)) THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa1`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa2`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``~BDs_OVERLAP bd_pa1 bd_pa2`` ``P ==> Q`` THEN
  PAT_ASSUM ``BD_EQ a m1 m2`` (fn thm => ASSUME_TAC (MATCH_MP BD_EQ_IMP_NDP_UNMODIFIED_lemma thm)) THEN
  MATCH_MP_TAC NDP_UNMODIFIED_TRANS_lemma THEN
  EXISTS_TAC ``(cppi_ram_write_step : cppi_ram_write_step_type) CPPI_RAM bd_pa2`` THEN
  ASM_REWRITE_TAC [cppi_ram_write_EQ_cppi_ram_write_step_first_cppi_ram_write_lemma]);



val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVES_NDP_OF_NON_OVERLAPPING_OR_WRITTEN_BD_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_REVERSED_PRESERVES_NDP_OF_NON_OVERLAPPING_OR_WRITTEN_BD_lemma",
  ``!cppi_ram_write_step_bd_pas bd_pa.
    ~BD_LIST_OVERLAP (MAP SND cppi_ram_write_step_bd_pas) /\
    (BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas) \/ MEM bd_pa (MAP SND cppi_ram_write_step_bd_pas)) /\
    BD_IN_CPPI_RAM bd_pa /\
    BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas) /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  Induct THENL
  [
   REWRITE_TAC [REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def, NDP_UNMODIFIED_def]
   ,
   Cases_on `h` THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``P \/ Q`` listTheory.MEM THEN
   KEEP_ASM_RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)`` ``!x.P`` THEN
   ASSUME_TAC (UNDISCH (SPECL [``r : bd_pa_type``, ``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``] NO_OVERLAP_IMP_NO_OVERLAP_TAIL_lemma)) THEN
   ASM_RW_ASM_TAC ``~BD_LIST_OVERLAP (MAP SND cppi_ram_write_step_bd_pas)`` ``!x.P`` THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``bd_pa : bd_pa_type`` thm)) THEN
   RW_ASM_TAC ``BDs_IN_CPPI_RAM (h::t)`` BDs_IN_CPPI_RAM_HD_TL_EQ_lemma THEN
   SPLIT_ASM_TAC THEN
   Cases_on `BD_NOT_OVERLAP_BDs bd_pa (r::MAP SND cppi_ram_write_step_bd_pas)` THENL
   [
    RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa (r::MAP SND cppi_ram_write_step_bd_pas)`` BD_NOT_OVERLAP_BDs_HD_TL_EQ_lemma THEN
    SPLIT_ASM_TAC THEN
    ASM_RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
    KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
    ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_pa : bd_pa_type``, ``r : bd_pa_type``, ``q : cppi_ram_write_step_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] NON_OVERLAPPING_BDs_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_REVERSED_PRESERVES_NDP_IMP_REVERSED_STEP_PRESERVES_NDP_lemma)))) THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~BD_NOT_OVERLAP_BDs bd_pa l`` ``P \/ Q``
   ] THEN
   Cases_on `bd_pa = r` THENL
   [
    ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``r : bd_pa_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_REVERSED_PRESERVES_NON_OVERLAPPING_BD_PA_lemma)))) THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``r : bd_pa_type``, ``q : cppi_ram_write_step_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] CPPI_RAM_WRITE_STEP_AND_REVERSED_PRESERVE_NDP_AT_BD_PA_lemma)))) THEN
    ASM_REWRITE_TAC []
    ,
    KEEP_ASM_RW_ASM_TAC ``bd_pa <> r`` ``P \/ Q``
   ] THEN
   KEEP_ASM_RW_ASM_TAC ``MEM bd_pa (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON (SPECL [``bd_pa : bd_pa_type``, ``r : bd_pa_type``, ``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``] DISTINCT_BD_PA_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_BDs_lemma))))))) THEN
   MATCH_MP_TAC REVERSED_CPPI_RAM_WRITE_PRESERVES_NDP_AND_STEP_WRITES_NON_OVERLAPPING_BD_IMP_NDP_PRESERVED_lemma THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
   ASM_REWRITE_TAC []
  ]);

val CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_PRESERVES_NDP_OF_NON_OVERLAPPING_OR_WRITTEN_BD_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_CPPI_RAM_WRITE_PRESERVES_NDP_OF_NON_OVERLAPPING_OR_WRITTEN_BD_lemma",
  ``!cppi_ram_write_step_bd_pas bd_pa.
    ~BD_LIST_OVERLAP (MAP SND cppi_ram_write_step_bd_pas) /\
    (BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas) \/ MEM bd_pa (MAP SND cppi_ram_write_step_bd_pas)) /\
    BD_IN_CPPI_RAM bd_pa /\
    BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas) /\
    CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)
    ==>
    CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA cppi_ram_write_step_bd_pas bd_pa``,
  Induct THENL
  [
   REWRITE_TAC [CPPI_RAM_WRITE_PRESERVES_NDP_OF_BD_AT_BD_PA_def] THEN
   REWRITE_TAC [cppi_ram_write_def] THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_def] THEN
   REWRITE_TAC [reverse_cppi_ram_write_step_bd_pas_with_accumulator_def] THEN
   REWRITE_TAC [reversed_cppi_ram_write_def] THEN
   REWRITE_TAC [NDP_UNMODIFIED_def]
   ,
   Cases_on `h` THEN
   GEN_TAC THEN
   REWRITE_TAC [listTheory.MAP] THEN
   REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_HD_TL_EQ_lemma] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   RW_ASM_TAC ``P \/ Q`` listTheory.MEM THEN
   KEEP_ASM_RW_ASM_TAC ``CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP (MAP FST cppi_ram_write_step_bd_pas)`` ``!x.P`` THEN
   ASSUME_TAC (UNDISCH (SPECL [``r : bd_pa_type``, ``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``] NO_OVERLAP_IMP_NO_OVERLAP_TAIL_lemma)) THEN
   ASM_RW_ASM_TAC ``~BD_LIST_OVERLAP (MAP SND cppi_ram_write_step_bd_pas)`` ``!x.P`` THEN
   PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``bd_pa : bd_pa_type`` thm)) THEN
   RW_ASM_TAC ``BDs_IN_CPPI_RAM (h::t)`` BDs_IN_CPPI_RAM_HD_TL_EQ_lemma THEN
   SPLIT_ASM_TAC THEN
   Cases_on `BD_NOT_OVERLAP_BDs bd_pa (r::MAP SND cppi_ram_write_step_bd_pas)` THENL
   [
    RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa (r::MAP SND cppi_ram_write_step_bd_pas)`` BD_NOT_OVERLAP_BDs_HD_TL_EQ_lemma THEN
    SPLIT_ASM_TAC THEN
    ASM_RW_ASM_TAC ``BD_NOT_OVERLAP_BDs bd_pa (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
    KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
    ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_pa : bd_pa_type``, ``r : bd_pa_type``, ``q : cppi_ram_write_step_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] NON_OVERLAPPING_BDs_CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_IMP_STEP_PRESERVES_NDP_lemma)))) THEN
    ASM_REWRITE_TAC []
    ,
    ASM_RW_ASM_TAC ``~BD_NOT_OVERLAP_BDs bd_pa l`` ``P \/ Q``
   ] THEN
   Cases_on `bd_pa = r` THENL
   [
    ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``r : bd_pa_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] CPPI_RAM_WRITE_STEPs_WRITE_BD_AND_PRESERVE_NDP_IMP_PRESERVES_NON_OVERLAPPING_BD_PA_lemma)))) THEN
    RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
    SPLIT_ASM_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``r : bd_pa_type``, ``q : cppi_ram_write_step_type``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] CPPI_RAM_WRITE_STEP_AND_PRESERVE_NDP_AT_BD_PA_lemma)))) THEN
    ASM_REWRITE_TAC []
    ,
    KEEP_ASM_RW_ASM_TAC ``bd_pa <> r`` ``P \/ Q``
   ] THEN
   KEEP_ASM_RW_ASM_TAC ``MEM bd_pa (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   KEEP_ASM_RW_ASM_TAC ``BD_IN_CPPI_RAM bd_pa`` ``P ==> Q`` THEN
   ASM_RW_ASM_TAC ``BDs_IN_CPPI_RAM (MAP SND cppi_ram_write_step_bd_pas)`` ``P ==> Q`` THEN
   ASSUME_TAC (REWRITE_RULE [boolTheory.IMP_CLAUSES] (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON (SPECL [``bd_pa : bd_pa_type``, ``r : bd_pa_type``, ``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``] DISTINCT_BD_PA_IN_NON_OVERLAPPING_LIST_IMP_NON_OVERLAPPING_BDs_lemma))))))) THEN
   MATCH_MP_TAC CPPI_RAM_WRITE_PRESERVES_NDP_AND_STEP_WRITES_NON_OVERLAPPING_BD_IMP_NDP_PRESERVED_lemma THEN
   RW_ASM_TAC ``CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP q`` CPPI_RAM_WRITE_STEP_WRITES_BD_AND_PRESERVES_NDP_def THEN
   ASM_REWRITE_TAC []
  ]);

val _ = export_theory();

