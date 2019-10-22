open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open bd_listTheory;
open bdTheory;
open rxInvariantWellDefinedLemmasTheory;
open rx_bd_queueTheory;

val _ = new_theory "rxInvariantWellDefinedRX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemmas";

val RX_MEM_BD_QUEUE_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma = store_thm (
  "RX_MEM_BD_QUEUE_WELL_DEFINED_IMP_BD_WELL_DEFINED_lemma",
  ``!bd_pa q CPPI_RAM.
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED q CPPI_RAM /\
    MEM bd_pa q
    ==>
    RX_INVARIANT_BD_WELL_DEFINED (rx_read_bd bd_pa CPPI_RAM)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_WELL_DEFINED_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
  PAT_ASSUM ``f a`` (fn thm => ASSUME_TAC (REWRITE_RULE [BETA_CONV (concl thm)] thm)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_WELL_DEFINED_IMP_SUFFIX_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_WELL_DEFINED_IMP_SUFFIX_lemma",
  ``!q1 q2 CPPI_RAM.
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (q1 ++ q2) CPPI_RAM
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED q2 CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_WELL_DEFINED_def] THEN
  REWRITE_TAC [listTheory.EVERY_APPEND] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val EQ_BDs_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma = store_thm (
  "EQ_BDs_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma",
  ``!q CPPI_RAM CPPI_RAM'.
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED q CPPI_RAM /\
    EQ_BDs q CPPI_RAM CPPI_RAM'
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED q CPPI_RAM'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_WELL_DEFINED_def] THEN
  REWRITE_TAC [EQ_BDs_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``e : bd_pa_type`` thm))) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``e : bd_pa_type`` thm))) THEN
  ASSUME_TAC (UNDISCH (GSYM (SPECL [``e : bd_pa_type``, ``CPPI_RAM : cppi_ram_type``, ``CPPI_RAM' : cppi_ram_type``] BD_EQ_IMP_rx_read_bd_EQ_lemma))) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_RX_SEEN_BDs_PRESERVES_WELL_DEFINED_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_RX_SEEN_BDs_PRESERVES_WELL_DEFINED_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas /\
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue (nic_delta nic)) (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC EQ_BDs_PRESERVES_RX_INVARIANT_BD_QUEUE_WELL_DEFINED_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic`` NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NIC_DELTA_RX_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

