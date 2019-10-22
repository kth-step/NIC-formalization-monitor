open HolKernel Parse boolLib bossLib;
open helperTactics;
open stateTheory;
open bd_queueTheory;
open bd_queue_preservation_lemmasTheory;
open bdTheory;
open CPPI_RAMTheory;

val _ = new_theory "tx_bd_queue";

val tx_bd_queue_def = Define `tx_bd_queue (nic : nic_state) =
  bd_queue nic.tx.sop_bd_pa nic.regs.CPPI_RAM`;

val TX_BD_QUEUE_IMP_tx_bd_queue_lemma = store_thm (
  "TX_BD_QUEUE_IMP_tx_bd_queue_lemma",
  ``!nic q.
    BD_QUEUE q nic.tx.sop_bd_pa nic.regs.CPPI_RAM
    ==>
    (tx_bd_queue nic = q)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [tx_bd_queue_def] THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : 32 word list``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma = store_thm (
  "TX_BD_QUEUE_IMP_TX_BD_QUEUE_tx_bd_queue_lemma",
  ``!nic q.
    BD_QUEUE q nic.tx.sop_bd_pa nic.regs.CPPI_RAM
    ==>
    BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [tx_bd_queue_def] THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : 32 word list``, ``nic.tx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val EQ_SOP_BD_PA_AND_CPPI_RAM_AND_TX_INVARIANT_BD_QUEUE_FINITE_IMP_EQ_BD_QUEUES_lemma = store_thm (
  "EQ_SOP_BD_PA_AND_CPPI_RAM_AND_TX_INVARIANT_BD_QUEUE_FINITE_IMP_EQ_BD_QUEUES_lemma",
  ``!nic nic'.
    (nic'.tx.sop_bd_pa = nic.tx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [tx_bd_queue_def] THEN
  ASM_REWRITE_TAC []);

val TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma = store_thm (
  "TX_BD_QUEUE_EQ_TX_STATE_EQ_TX_BD_QUEUE_BDs_IMP_EQ_TX_BD_QUEUEs_lemma",
  ``!nic nic'.
    BD_QUEUE (tx_bd_queue nic) nic.tx.sop_bd_pa nic.regs.CPPI_RAM /\
    (nic'.tx = nic.tx) /\
    EQ_BDs (tx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (tx_bd_queue nic' = tx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [tx_bd_queue_def] THEN
  MATCH_MP_TAC BD_QUEUE_EQ_BDs_IMP_EQ_BD_QUEUEs_lemma THEN
  EXISTS_TAC ``tx_bd_queue nic`` THEN
  ASM_REWRITE_TAC []);

val tx_read_ndp_EQ_read_ndp_lemma = store_thm (
  "tx_read_ndp_EQ_read_ndp_lemma",
  ``!bd_pa CPPI_RAM.
    (tx_read_bd bd_pa CPPI_RAM).ndp = read_ndp bd_pa CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [read_ndp_def, tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC [GSYM bd_data_updates_eq_literal] THEN
  Cases_on `b` THEN
  REWRITE_TAC [bd_data_fn_updates, combinTheory.K_THM, bd_data_ndp]);

val BD_EQ_IMP_TX_BD_EQ_lemma = store_thm (
  "BD_EQ_IMP_TX_BD_EQ_lemma",
  ``!bd_pa CPPI_RAM CPPI_RAM'.
    BD_EQ bd_pa CPPI_RAM CPPI_RAM'
    ==>
    (tx_read_bd bd_pa CPPI_RAM = tx_read_bd bd_pa CPPI_RAM')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [tx_read_bd_def, LET_DEF] THEN
  BETA_TAC THEN
  BETA_TAC THEN
  (fn g =>
     let fun t w = ASSUME_TAC (UNDISCH (REWRITE_RULE [blastLib.BBLAST_PROVE ``^w <=+ 3w : 32 word``] (SPECL [``bd_pa : 32 word``, ``CPPI_RAM : 13 word -> 8 word``, ``CPPI_RAM' : 13 word -> 8 word``, w] BD_EQ_IMP_BD_WORDS_EQ_lemma)))
     in
     (t ``0w : 32 word`` THEN t ``1w : 32 word`` THEN t ``2w : 32 word`` THEN t ``3w : 32 word``) g
     end) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();
