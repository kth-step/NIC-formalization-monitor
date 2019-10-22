open HolKernel Parse boolLib bossLib;
open helperTactics;
open rxInvariantWellDefinedTheory;
open rx_bd_queueTheory;
open bd_listTheory;
open rx_state_definitionsTheory;
open bd_queueTheory;
open rx_state_lemmasTheory;
open rxTheory;
open rx_transition_definitionsTheory;
open it_state_definitionsTheory;
open bd_queue_preservation_lemmasTheory;

val _ = new_theory "rxInvariantWellDefinedLemmas";

(********************************************************)
(*Lemmas about invariants of the reception queue*********)
(********************************************************)

val RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic
    =
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  EQ_TAC THENL
  [
   DISCH_TAC THEN
   PAT_ASSUM ``P`` (fn thm => CHOOSE_TAC thm) THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   DISCH_TAC THEN
   EXISTS_TAC ``rx_bd_queue nic`` THEN
   ASM_REWRITE_TAC []
  ]);

val RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_HD_TL_EQ_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_HD_TL_EQ_lemma",
  ``!bd_pa q.
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (bd_pa::q)
    =
    BD_LOCATION_DEFINED bd_pa /\ RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_def, listTheory.EVERY_DEF]);

val RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_MEM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_MEM_lemma",
  ``!bd_pa q.
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q /\
    MEM bd_pa q
    ==>
    BD_LOCATION_DEFINED bd_pa``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_def, listTheory.EVERY_MEM] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => MATCH_MP_TAC thm) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma",
  ``!q.
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q
    ==>
    BDs_IN_CPPI_RAM q``,
  Induct THENL
  [
   REWRITE_TAC [BDs_IN_CPPI_RAM_def, listTheory.EVERY_DEF]
   ,
   GEN_TAC THEN
   REWRITE_TAC [RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_HD_TL_EQ_lemma] THEN
   REWRITE_TAC [BDs_IN_CPPI_RAM_HD_TL_EQ_lemma] THEN
   REWRITE_TAC [CPPI_RAMTheory.BD_LOCATION_DEFINED_def] THEN
   DISCH_TAC THEN
   SPLIT_ASM_TAC THEN
   ASM_RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
  ]);

(********************************************************)
(*Rewrite Lemmas about invariants of the reception queue*)
(********************************************************)




(********************************************************)
(*Lemmas about membership of buffer descriptor addresses*)
(********************************************************)

val RX_INVARIANT_BD_QUEUE_STRUCTURE_MEM_UNSEEN_IMP_MEM_BD_QUEUE_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_STRUCTURE_MEM_UNSEEN_IMP_MEM_BD_QUEUE_lemma",
  ``!nic bd_pa.
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    MEM bd_pa (rx_unseen_bd_queue nic)
    ==>
    MEM bd_pa (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_REWRITE_TAC [listTheory.MEM_APPEND]);

val RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma",
  ``!nic bd_pa rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    MEM bd_pa rx_seen_bd_queue /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    ~MEM bd_pa (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q a m`` RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma THEN
  ASSUME_TAC (UNDISCH (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPEC_ALL RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma))))))) THEN
  ASM_REWRITE_TAC []);

val RX_BD_QUEUE_FINITE_idle_NOT_EMPTY_BD_QUEUE_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_FINITE_idle_NOT_EMPTY_BD_QUEUE_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_STATE_IDLE nic /\
    (nic.rx.sop_bd_pa <> 0w)
    ==>
    MEM nic.rx.sop_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [rx_unseen_bd_queue_def, RX_STATE_IDLE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q a m`` (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_BD_QUEUE_FINITE_write_cp_NOT_EMPTY_BD_QUEUE_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_FINITE_write_cp_NOT_EMPTY_BD_QUEUE_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_STATE_WRITE_CP nic /\
    (nic.rx.sop_bd_pa <> 0w)
    ==>
    MEM nic.rx.sop_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [rx_unseen_bd_queue_def, RX_STATE_WRITE_CP_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [stateTheory.rx_abstract_state_case_def] THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q a m`` (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_RX_BD_QUEUE_IMP_MEM_SOP_BD_PA_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_RX_BD_QUEUE_IMP_MEM_SOP_BD_PA_SEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_FETCH_NEXT_BD nic /\
    ~RX_CURRENT_BD_SOP nic.rx /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    MEM nic.rx.sop_bd_pa rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``¬RX_CURRENT_BD_SOP nic.rx`` RX_CURRENT_BD_SOP_def THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``nic.rx.current_bd_pa``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_fetch_next_bd_BD_QUEUE_CURRENT_BD_PA_IMP_BD_QUEUE_rx_unseen_bd_queue_lemma)))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``rx_seen_bd_queue : 32 word list``, ``rx_unseen_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEMBER_DISTINCT_START_IMP_NOT_EMPTY_PREFIX_lemma)))) THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_RW_ASM_TAC ``rx_seen_bd_queue = h::t`` ``rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic`` THEN
  RW_ASM_TAC ``rx_bd_queue nic = h::t ++ rx_unseen_bd_queue nic`` listTheory.APPEND THEN
  ASM_RW_ASM_TAC ``rx_bd_queue nic = h::(t ++ rx_unseen_bd_queue nic)`` ``BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``h : 32 word``, ``nic.rx.sop_bd_pa``, ``t ++ rx_unseen_bd_queue nic``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_HEAD_EQ_START_lemma)) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_BD_QUEUE_FINITE_RX_STATE_FETCH_NEXT_BD_MEM_CURRENT_BD_PA_RX_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_FINITE_RX_STATE_FETCH_NEXT_BD_MEM_CURRENT_BD_PA_RX_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_FETCH_NEXT_BD nic /\
    ~RX_CURRENT_BD_SOP nic.rx /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    ~MEM nic.rx.sop_bd_pa (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_RX_BD_QUEUE_IMP_MEM_SOP_BD_PA_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``nic : nic_state``, ``nic.rx.sop_bd_pa``, ``rx_seen_bd_queue : 32 word list``] RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma))))))) THEN
  ASM_REWRITE_TAC []);

val RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_SEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    MEM nic.rx.sop_bd_pa rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` (fn thm => ASSUME_TAC (GSYM (UNDISCH_ALL (hd (IMP_CANON (REWRITE_RULE [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] thm)))))) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM`` RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``,  ``nic.rx.current_bd_pa``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] MEM_BD_QUEUE_NOT_ZERO_lemma)))))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q : 32 word list``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_RW_ASM_TAC ``q = nic.rx.current_bd_pa::t`` ``BD_QUEUE q nic.rx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  RW_ASM_TAC ``BD_QUEUE (nic.rx.current_bd_pa::t) nic.rx.current_bd_pa nic.regs.CPPI_RAM`` BD_QUEUE_def THEN
  PAT_ASSUM ``P /\ Q`` (fn thm => ASSUME_TAC (CONJUNCT2 thm)) THEN
  ASSUME_TAC (GSYM (UNDISCH (SPECL [``t : 32 word list``, ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma))) THEN
  ASSUME_TAC (GSYM (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma))))) THEN
  ASM_RW_ASM_TAC ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp`` ``t = bd_queue (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM = rx_unseen_bd_queue nic`` ``t = bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``t = rx_unseen_bd_queue nic`` ``BD_QUEUE t (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``rx_seen_bd_queue : 32 word list``, ``rx_unseen_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEMBER_IMP_MEMBER_START_BD_PA_PREFIX_lemma)))) THEN
  ASM_REWRITE_TAC []);

val RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    ~MEM nic.rx.sop_bd_pa (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_BD_QUEUE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_SEEN_BD_QUEUE_lemma)))) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``nic : nic_state``, ``nic.rx.sop_bd_pa``, ``rx_seen_bd_queue : 32 word list``] RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma))))))) THEN
  ASM_REWRITE_TAC []);

val RX_write_cp_BD_QUEUE_CURRENT_BD_PA_EQ_SOP_BD_PA_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_write_cp_BD_QUEUE_CURRENT_BD_PA_EQ_SOP_BD_PA_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic /\
    nic.rx.sop_bd_pa <> 0w /\
    RX_STATE_WRITE_CP nic
    ==>
    MEM nic.rx.sop_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM`` RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma THEN
  ASSUME_TAC (GSYM (UNDISCH (SPEC_ALL RX_write_cp_IMP_unseen_bd_queue_EQ_bd_queue_lemma))) THEN
  ASM_RW_ASM_TAC ``rx_bd_queue nic = rx_unseen_bd_queue nic`` ``BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_unseen_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic
    ==>
    MEM nic.rx.current_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_RECEIVE_FRAME_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_idle_IMP_unseen_bd_queue_EQ_bd_queue_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic`` RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def THEN
  ASM_RW_ASM_TAC ``RX_STATE_IDLE nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``IT_STATE_INITIALIZED nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT (WEAKEN_TAC (fn term => is_eq term)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``~RX_BD_QUEUE_EMPTY nic`` RX_BD_QUEUE_EMPTY_def THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_BD_QUEUE_EQ_START_TL_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``bd_queue nic.rx.sop_bd_pa nic.regs.CPPI_RAM = nic.rx.sop_bd_pa::t'`` (GSYM rx_bd_queue_def) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic
    ==>
    MEM nic.rx.current_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
  ASSUME_TAC ((UNDISCH_ALL o hd o IMP_CANON) (SPECL [``rx_bd_queue nic : 32 word list``, ``nic.rx.current_bd_pa``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``rx_bd_queue nic : 32 word list``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] MEM_BD_QUEUE_NOT_ZERO_lemma)))))) THEN
  ASSUME_TAC (UNDISCH (SPECL [``q' : 32 word list``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_queue nic.rx.current_bd_pa nic.regs.CPPI_RAM``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/
     RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_RECEIVE_FRAME nic` THENL
  [
   MATCH_MP_TAC RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   MATCH_MP_TAC RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_SEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    MEM nic.rx.current_bd_pa rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM`` RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``nic.rx.current_bd_pa``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] MEMBER_OF_BD_QUEUE_IMP_START_OF_SUBQUEUE_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] MEM_BD_QUEUE_NOT_ZERO_lemma)))))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``q : 32 word list``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] NOT_ZERO_START_BD_PA_BD_QUEUE_IMP_BD_QUEUE_START_BD_PA_NDP_QUEUE_lemma)))) THEN
  COPY_ASM_TAC ``nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  REFLECT_ASM_TAC ``nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp`` ``BD_QUEUE (bd_queue (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM) (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (GSYM (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma))))) THEN
  ASM_RW_ASM_TAC ``bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM = rx_unseen_bd_queue nic`` ``BD_QUEUE (bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM) nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM`` ``BD_QUEUE (rx_unseen_bd_queue nic) nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``rx_seen_bd_queue : 32 word list``, ``rx_unseen_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] SUFFIX_EQ_BD_PA_NDPs_IMP_MEM_BD_PA_PREFIX_lemma)))) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_NOT_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    ~MEM nic.rx.current_bd_pa (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_SEEN_BD_QUEUE_lemma)))) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``nic : nic_state``, ``nic.rx.current_bd_pa``, ``rx_seen_bd_queue : 32 word list``] RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma))))))) THEN
  ASM_REWRITE_TAC []);

val RX_write_cp_NOT_EMPTY_BD_QUEUE_FINITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_write_cp_NOT_EMPTY_BD_QUEUE_FINITE_CURRENT_BD_PA_EQ_SOP_BD_PA_IMP_MEM_CURRENT_BD_PA_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    RX_STATE_WRITE_CP nic /\
    nic.rx.sop_bd_pa <> 0w
    ==>
    MEM nic.rx.current_bd_pa (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_BD_QUEUE_FINITE_write_cp_NOT_EMPTY_BD_QUEUE_IMP_MEM_SOP_BD_PA_UNSEEN_BD_QUEUE_lemma)))) THEN
  RW_ASM_TAC ``RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic`` RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CP nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_IDLE_FETCH_NEXT_BD_NOR_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic``,
  GEN_TAC THEN
  DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_IDLE_FETCH_NEXT_BD_NOR_WRITE_CP_lemma)) THEN
  ASM_REWRITE_TAC [RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def, RX_STATE_WRITE_CP_def]);

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_MEM_EOP_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_MEM_EOP_SEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic /\
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    MEM nic.rx.eop_bd_pa rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic`` ``P ==> Q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP(SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_SEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_NOT_MEM_EOP_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_NOT_MEM_EOP_UNSEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic /\
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic)
    ==>
    ~MEM nic.rx.eop_bd_pa (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_MEM_EOP_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH (UNDISCH (UNDISCH (REWRITE_RULE [boolTheory.IMP_CLAUSES] (hd (IMP_CANON (SPECL [``nic : nic_state``, ``nic.rx.eop_bd_pa``, ``rx_seen_bd_queue : 32 word list``] RX_BD_QUEUE_MEM_SEEN_BD_QUEUE_IMP_NOT_MEM_UNSEEN_BD_QUEUE_lemma))))))) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_NDP_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_NDP_UNSEEN_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    nic.rx.current_bd.ndp <> 0w
    ==>
    MEM nic.rx.current_bd.ndp (rx_unseen_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (CONJ_ANT_TO_HYP thm)) THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM`` RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEMBER_IMP_START_OF_NON_EMPTY_QUEUE_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  RW_ASM_TAC ``BD_QUEUE (nic.rx.current_bd_pa::t) nic.rx.current_bd_pa nic.regs.CPPI_RAM`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  REFLECT_ASM_TAC ``nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp`` ``BD_QUEUE t (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM`` THEN
  MATCH_MP_ASM_IMP_TAC ``BD_QUEUE t nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` BD_QUEUE_IMP_BD_QUEUE_bd_queue_lemma THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM``, ``nic.rx.current_bd.ndp``, ``nic.regs.CPPI_RAM``] BD_QUEUE_START_NOT_ZERO_IMP_BD_QUEUE_EQ_START_TL_lemma)))) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)))) THEN
  ASM_REWRITE_TAC [listTheory.MEM]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_CURRENT_BD_NDP_EQ_ZERO_OR_MEM_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_CURRENT_BD_NDP_EQ_ZERO_OR_MEM_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic
    ==>
    (nic.rx.current_bd.ndp = 0w) \/ MEM nic.rx.current_bd.ndp (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.current_bd.ndp = 0w` THEN
  ASM_REWRITE_TAC [] THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P \/ Q ==> R`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  MATCH_MP_TAC NON_LAST_IN_Q_THEN_NEXT_IN_Q_lemma THEN
  EXISTS_TAC ``nic.rx.sop_bd_pa`` THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  EXISTS_TAC ``nic.rx.current_bd_pa`` THEN
  KEEP_ASM_RW_ASM_TAC ``x = y`` ``~P`` THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma]);

(***************************************************************)
(*End of lemmas about membership of buffer descriptor addresses*)
(***************************************************************)


(***************************************************************)
(*Lemmas stating what state components the predicates depend on*)
(***************************************************************)

val RX_INVARIANT_NOT_DEAD_DEP_dead_lemma = store_thm (
  "RX_INVARIANT_NOT_DEAD_DEP_dead_lemma",
  ``!nic nic'.
    RX_INVARIANT_NOT_DEAD nic /\
    (nic'.dead = nic.dead)
    ==>
    RX_INVARIANT_NOT_DEAD nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_NOT_DEAD_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_FINITE_DEP_sop_bd_pa_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_FINITE_DEP_sop_bd_pa_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_BD_QUEUE_FINITE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_STRUCTURE_STATE_PROCESS_CURRENT_BD_DEP_current_bd_ndp_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_STRUCTURE_STATE_PROCESS_CURRENT_BD_DEP_current_bd_ndp_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic' /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic'``, 
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC ``nic' : nic_state`` RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)))) THEN
  ASM_RW_ASM_TAC ``nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp`` ``rx_unseen_bd_queue nic' = bd_queue nic'.rx.current_bd.ndp nic'.regs.CPPI_RAM`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM`` ``rx_unseen_bd_queue nic' = bd_queue nic.rx.current_bd.ndp nic'.regs.CPPI_RAM`` THEN
  REFLECT_ASM_TAC ``rx_unseen_bd_queue nic' = bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM = rx_unseen_bd_queue nic'`` ``rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``rx_unseen_bd_queue nic = rx_unseen_bd_queue nic'`` ``?x.P`` THEN
  ASSUME_TAC (GSYM (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma))))) THEN
  ASM_RW_ASM_TAC ``rx_bd_queue nic = rx_bd_queue nic'`` ``?x.P`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_NO_OVERLAP_DEP_sop_bd_pa_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_NO_OVERLAP_DEP_sop_bd_pa_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)))) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_DEP_sop_bd_pa_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_DEP_sop_bd_pa_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic')``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)))) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_WELL_DEFINED_NOT_idle_fetch_next_bd_write_cp_DEP_current_bd_ndp_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_WELL_DEFINED_NOT_idle_fetch_next_bd_write_cp_DEP_current_bd_ndp_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic' /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)))) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC ``nic' : nic_state`` RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)))) THEN
  ASM_RW_ASM_TAC ``nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp`` ``rx_unseen_bd_queue nic' = bd_queue nic'.rx.current_bd.ndp nic'.regs.CPPI_RAM`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM`` ``rx_unseen_bd_queue nic' = bd_queue nic.rx.current_bd.ndp nic'.regs.CPPI_RAM`` THEN
  REFLECT_ASM_TAC ``rx_unseen_bd_queue nic' = bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM = rx_unseen_bd_queue nic'`` ``rx_unseen_bd_queue nic = bd_queue nic.rx.current_bd.ndp nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``rx_unseen_bd_queue nic = rx_unseen_bd_queue nic'`` ``RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM`` THEN
  REFLECT_ASM_TAC ``nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM`` THEN
  ASM_RW_ASM_TAC ``nic.regs.CPPI_RAM = nic'.regs.CPPI_RAM`` ``RX_INVARIANT_BD_QUEUE_WELL_DEFINED (rx_unseen_bd_queue nic') nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_DEP_RX_BUFFER_OFFSET_lemma = store_thm (
  "RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_DEP_RX_BUFFER_OFFSET_lemma",
  ``!nic nic'.
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic /\
    (nic'.regs.RX_BUFFER_OFFSET = nic.regs.RX_BUFFER_OFFSET)
    ==>
    RX_INVARIANT_RX_BUFFER_OFFSET_ZERO nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_RX_BUFFER_OFFSET_ZERO_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_DEP_lemma = store_thm (
  "RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_DEP_lemma",
  ``!nic nic'.
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic : nic_state``] (GSYM RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_DEP_lemma))) THEN
  ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_STATE_PROCESS_CURRENT_BD_DEP_current_bd_ndp_current_bd_pa_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_STATE_PROCESS_CURRENT_BD_DEP_current_bd_ndp_current_bd_pa_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic' /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON thm)))) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_DEP_lemma = store_thm (
  "RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_DEP_lemma",
  ``!nic nic'.
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic /\
    (nic'.rx.state = nic.rx.state) /\
    (nic'.it.state = nic.it.state) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa)
    ==>
    RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_IDLE nic' ∧ IT_STATE_INITIALIZED nic'` THENL
  [
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic : nic_state``] (GSYM RX_STATE_IDLE_DEP_lemma))) THEN
   ASM_RW_ASM_TAC ``RX_STATE_IDLE nic`` ``P ==> Q`` THEN
   RW_ASM_TAC ``IT_STATE_INITIALIZED nic'`` IT_STATE_INITIALIZED_def THEN
   RW_ASM_TAC ``P ==> Q`` IT_STATE_INITIALIZED_def THEN
   ASM_RW_ASM_TAC ``nic'.it.state = nic.it.state`` ``nic'.it.state = init_initialized`` THEN
   ASM_RW_ASM_TAC ``nic.it.state = init_initialized`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic : nic_state``] (GSYM RX_STATE_WRITE_CP_DEP_lemma))) THEN
   ASM_RW_ASM_TAC ``RX_STATE_WRITE_CP nic`` ``P ==> Q`` THEN
   ASM_REWRITE_TAC []
  ]);

val RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_DEP_lemma = store_thm (
  "RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_DEP_lemma",
  ``!nic nic'.
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic /\
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp)
    ==>
    RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic : nic_state``] (GSYM RX_STATE_WRITE_CP_DEP_lemma))) THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CP nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_DEP_lemma = store_thm (
  "RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_DEP_lemma",
  ``!nic nic'.
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.it.state = nic.it.state) /\
    (nic'.rd.state = nic.rd.state) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic : nic_state``] (GSYM RX_STATES_INIT_NOT_BD_QUEUE_EMPTY_DEP_lemma))) THEN
  ASM_RW_ASM_TAC ``P \/ Q`` ``P ==> Q`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_STATE_FETCH_OR_PROCESS_CURRENT_BD_DEP_current_bd_pa_sop_bd_pa_CPPI_RAM_lemma = store_thm (
  "RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_STATE_FETCH_OR_PROCESS_CURRENT_BD_DEP_current_bd_pa_sop_bd_pa_CPPI_RAM_lemma",
  ``!nic nic'.
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic' /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_RX_SOP_BD_PA_CPPI_RAM_IMP_EX_RX_BD_QUEUE_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_DEP_lemma = store_thm (
  "RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_DEP_lemma",
  ``!nic nic'.
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic /\
    (nic'.rx.state = nic.rx.state) /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic' : nic_state``, ``nic : nic_state``] (GSYM RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_DEP_lemma))) THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_RX_POST_PROCESS_DEP_eop_bd_pa_current_bd_pa_lemma = store_thm (
  "RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_RX_POST_PROCESS_DEP_eop_bd_pa_current_bd_pa_lemma",
  ``!nic nic'.
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic /\
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic' /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa)
    ==>
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_DEP_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_DEP_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    (nic'.rx.state = nic.rx.state) /\
    (nic'.it.state = nic.it.state) /\
    (nic'.rd.state = nic.rd.state) /\
    (nic'.rx.sop_bd_pa = nic.rx.sop_bd_pa) /\
    (nic'.rx.current_bd_pa = nic.rx.current_bd_pa) /\
    (nic'.rx.eop_bd_pa = nic.rx.eop_bd_pa) /\
    (nic'.rx.current_bd.ndp = nic.rx.current_bd.ndp) /\
    (nic'.regs.CPPI_RAM = nic.regs.CPPI_RAM)
    ==>
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic'``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_DEP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_DEP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_write_cp_IMP_CURRENT_BD_PA_EQ_CURRENT_BD_NDP_DEP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_DEP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_DEP_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_FINITE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_FINITE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_bd_queue nic' = rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_BD_QUEUE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma]);

val RX_STATE_IDLE_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_IDLE_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_STATE_IDLE nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_DEP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_idle_IMP_unseen_bd_queue_EQ_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` RX_idle_IMP_unseen_bd_queue_EQ_bd_queue_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_FETCH_NEXT_BD_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``, ``nic.rx.current_bd_pa``] EQ_BD_QUEUE_START_MEM_IMP_BD_QUEUE_MEM_START_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SYM (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_CURRENT_BD_PA_EQ_lemma))) THEN
  ASM_RW_ASM_TAC ``nic.rx.current_bd_pa = nic'.rx.current_bd_pa`` ``BD_QUEUE q' nic.rx.current_bd_pa nic'.regs.CPPI_RAM`` THEN
  ASSUME_TAC (SYM (UNDISCH (SPECL [``q' : bd_pa_type list``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma))) THEN
  ASSUME_TAC (UNDISCH (SPECL [``q' : bd_pa_type list``, ``nic'.rx.current_bd_pa``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_DEP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_NEXT_BD_QUEUE_EQ_BDs_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_NEXT_BD_QUEUE_EQ_BDs_lemma",
  ``!nic nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    ?q.
    BD_QUEUE q (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM) nic.regs.CPPI_RAM /\
    EQ_BDs q nic.regs.CPPI_RAM nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEM_IMP_BD_QUEUE_SPLIT_lemma)) THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``q = q' ++ q'' ++ q'''`` ``EQ_BDs q m m'`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``q' ++ [nic.rx.current_bd_pa]``, ``q'' : bd_pa_type list``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] EQ_BDs_IMP_EQ_SUFFIX_BDs_lemma)) THEN
  EXISTS_TAC ``q'' : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_NEXT_BD_QUEUE_EQ_BDs_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (SYM (UNDISCH thm))) THEN
  ASM_RW_ASM_TAC ``read_ndp a m = x`` ``BD_QUEUE q a m`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``nic.rx.current_bd.ndp``, ``nic.regs.CPPI_RAM``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_EQ_BDs_IMP_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (SYM (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_CURRENT_BD_NDP_EQ_lemma))) THEN
  ASM_RW_ASM_TAC ``nic.rx.current_bd.ndp = nic'.rx.current_bd.ndp`` ``BD_QUEUE q nic.rx.current_bd.ndp nic'.regs.CPPI_RAM`` THEN  
  ASSUME_TAC (SYM (UNDISCH (SPECL [``q : bd_pa_type list``, ``nic.rx.current_bd.ndp``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma))) THEN
  ASSUME_TAC (UNDISCH (SPECL [``q : bd_pa_type list``, ``nic'.rx.current_bd.ndp``, ``nic'.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma)) THEN
  ASM_RW_ASM_TAC ``q = bd_queue a m`` ``bd_queue a m = q`` THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_DEP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_CP_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CP_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_STATE_WRITE_CP nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_EQ_RX_STATE_EQ_RX_BD_QUEUE_BDs_IMP_EQ_RX_BD_QUEUEs_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_EQ_IMP_RX_STATE_EQ_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CP_DEP_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_write_cp_IMP_unseen_bd_queue_EQ_bd_queue_lemma)) THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` RX_write_cp_IMP_unseen_bd_queue_EQ_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_SUBINVARIANT_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_SUBINVARIANT_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    (nic'.rx = nic.rx) /\
    EQ_BDs (rx_bd_queue nic) nic.regs.CPPI_RAM nic'.regs.CPPI_RAM
    ==>
    (rx_unseen_bd_queue nic' = rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (SPEC_ALL RX_STATE_CASE_lemma) THEN
  Cases_on `RX_STATE_IDLE nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_FETCH_NEXT_BD nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CP_IMP_EQ_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(**********************************************************************)
(*End of lemmas stating what state components the predicates depend on*)
(**********************************************************************)



(*******************************************************************)
(*Lemmas concerning the membership of current_bd_pa in rx_bd_queue *)
(*******************************************************************)

val RX_STATE_IDLE_NIC_IT_STATE_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_AND_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_IDLE_NIC_IT_STATE_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_AND_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_STATE_RECEIVE_FRAME_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_IDLE nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``IT_STATE_INITIALIZED nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_START_BD_PA_NEQ_ZERO_IMP_MEM_START_BD_PA_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  RW_ASM_TAC ``~RX_BD_QUEUE_EMPTY nic`` RX_BD_QUEUE_EMPTY_def THEN
  ASM_REWRITE_TAC []);

val RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_RX_SOP_BD_PA_NEQ_ZERO_OR_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_FETCH_NEXT_BD nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_NIC_IT_STATE_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_AND_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``P \/ Q`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_WRITE_CURRENT_BD_PA nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma THEN
  REWRITE_TAC [RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_AND_NOT_WRITE_RX_SOP_BD_PA_def] THEN
  ASM_REWRITE_TAC []);

val RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_OR_FETCH_NEXT_BD_RX_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_RECEIVE_FRAME nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_NIC_IT_STATE_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_AND_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

(**************************************************************************)
(*End of lemmas concerning the membership of current_bd_pa in rx_bd_queue *)
(**************************************************************************)


(***************************************************************)
(*Lemmas concerning the membership of eop_bd_pa in rx_bd_queue *)
(***************************************************************)

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EQ_CURRENT_BD_PA_IMP_MEM_EOP_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EQ_CURRENT_BD_PA_IMP_MEM_EOP_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic
    ==>
    MEM nic.rx.eop_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA_def THEN
  ASM_RW_ASM_TAC ``RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_EOP_OR_EOP_SOP_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_EOP_OR_EOP_SOP_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_WRITE_EOP_OR_EOP_SOP nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.eop_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_WRITE_EOP_OR_EOP_SOP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EQ_CURRENT_BD_PA_IMP_MEM_EOP_BD_PA_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.eop_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EQ_CURRENT_BD_PA_IMP_MEM_EOP_BD_PA_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

(**********************************************************************)
(*End of lemmas concerning the membership of eop_bd_pa in rx_bd_queue *)
(**********************************************************************)



(***************************************************************)
(*Lemmas concerning the membership of sop_bd_pa in rx_bd_queue *)
(***************************************************************)

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic
    ==>
    MEM nic.rx.sop_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  Cases_on `rx_bd_queue nic` THENL
  [
   RW_ASM_TAC ``MEM a q`` listTheory.MEM THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   RW_ASM_TAC ``BD_QUEUE q a m`` BD_QUEUE_def THEN
   ASM_REWRITE_TAC [listTheory.MEM]
  ]);

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_STRUCTURE_SUPPORT_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_STRUCTURE_SUPPORT_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma",
  ``!nic.
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    MEM nic.rx.sop_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

(**********************************************************************)
(*End of lemmas concerning the membership of sop_bd_pa in rx_bd_queue *)
(**********************************************************************)

(***************************************************************)
(*Lemmas concerning the membership of eop_bd_pa in rx_bd_queue *)
(***************************************************************)

val MEM_PREFIX_IMP_MEM_LIST_lemma = store_thm (
  "MEM_PREFIX_IMP_MEM_LIST_lemma",
  ``!(l : bd_pa_type list) l1 l2 e.
    (l = l1 ++ l2) /\
    MEM e l1
    ==>
    MEM e l``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [listTheory.MEM_APPEND]);

val RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_AND_BD_STRUCTURE_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_AND_BD_STRUCTURE_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_INVARIANT_STATE_WRITE_CPPI_RAM_POST_PROCESS_IMP_EOP_EQ_CURRENT_BD_PA nic /\
    RX_STATE_WRITE_CPPI_RAM_POST_PROCESS nic
    ==>
    MEM nic.rx.eop_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_EOP_EOQ_CURRENT_BD_PA_IMP_MEM_EOP_SEEN_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL [``rx_bd_queue nic``, ``rx_seen_bd_queue : bd_pa_type list``, ``rx_unseen_bd_queue nic``, ``nic.rx.eop_bd_pa``] MEM_PREFIX_IMP_MEM_LIST_lemma)))) THEN
  ASM_REWRITE_TAC []);


(**********************************************************************)
(*End of lemmas concerning the membership of eop_bd_pa in rx_bd_queue *)
(**********************************************************************)





(*********************************)
(**Start of miscellaneous lemmas**)
(*********************************)

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_NEXT_SOP_BD_PA_EQ_CURRENT_BD_NDP_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma",
  ``!nic nic'.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    (nic'.rx.sop_bd_pa = nic.rx.current_bd.ndp) /\
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic'.regs.CPPI_RAM /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    BD_QUEUE (rx_bd_queue nic') nic'.rx.sop_bd_pa nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `nic.rx.current_bd.ndp = 0w` THENL
  [
   ASSUME_TAC (SPEC ``nic'.regs.CPPI_RAM`` BD_QUEUE_EMPTY_START_ZERO_lemma) THEN
   ASM_RW_ASM_TAC ``x = 0w`` ``nic'.rx.sop_bd_pa = nic.rx.current_bd.ndp`` THEN
   REFLECT_ASM_TAC ``x = y`` THEN
   ASM_RW_ASM_TAC ``0w = nic'.rx.sop_bd_pa`` ``BD_QUEUE q a m`` THEN
   ASSUME_TAC (UNDISCH (SPECL [``nic' : nic_state``, ``[] : bd_pa_type list``] RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
   SPLIT_ASM_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_BD_QUEUE_FINITE_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_CURRENT_BD_NDP_UNSEEN_BD_QUEUE_lemma)))) THEN
   RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_def THEN
   REFLECT_ASM_TAC ``nic'.rx.sop_bd_pa = nic.rx.current_bd.ndp`` THEN
   ASM_RW_ASM_TAC ``nic.rx.current_bd.ndp = nic'.rx.sop_bd_pa`` ``MEM e l`` THEN
   PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
   ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL RX_BD_QUEUE_NEXT_SOP_BD_PA_MEM_UNSEEN_BD_QUEUE_IMP_NEXT_BD_QUEUE_lemma)))) THEN
   ASM_REWRITE_TAC []
  ]);

val RX_STATE_IDLE_INIT_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma",
  ``!nic.
    RX_STATE_RECEIVE_FRAME nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    nic.rx.current_bd_pa <> 0w``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_idle_initialized_write_cp_IMP_CURRENT_BD_PA_EQ_SOP_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_STATE_RECEIVE_FRAME nic`` RX_STATE_RECEIVE_FRAME_def THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_IDLE nic`` ``P ==> Q`` THEN
  ASM_RW_ASM_TAC ``IT_STATE_INITIALIZED nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``~RX_BD_QUEUE_EMPTY nic`` RX_BD_QUEUE_EMPTY_def THEN
  ASM_REWRITE_TAC []);

val RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma = store_thm (
  "RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma",
  ``!nic.
    RX_STATE_FETCH_NEXT_BD nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    nic.rx.current_bd_pa <> 0w``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_FETCH_NEXT_BD_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_BD_QUEUE_IMP_RX_BD_QUEUE_rx_bd_queue_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] MEM_BD_QUEUE_NOT_ZERO_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_STATE_IDLE_INIT_INITIALIZED_SOP_BD_PA_NEQ_ZERO_OR_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma = store_thm (
  "RX_STATE_IDLE_INIT_INITIALIZED_SOP_BD_PA_NEQ_ZERO_OR_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma",
  ``!nic.
    (RX_STATE_RECEIVE_FRAME nic \/ RX_STATE_FETCH_NEXT_BD nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    nic.rx.current_bd_pa <> 0w``,
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  Cases_on `RX_STATE_FETCH_NEXT_BD nic` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_FETCH_NEXT_BD_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_IDLE_INIT_INITIALIZED_SOP_BD_PA_NEQ_ZERO_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_RX_CURRENT_BD_PA_NEQ_ZERO_lemma)) THEN
   ASM_REWRITE_TAC []
  ]);



(*******************************)
(**End of miscellaneous lemmas**)
(*******************************)

(*******************************************************************)
(**Start of preservation lemmas for reception transition functions**)
(*******************************************************************)

val RX_NIC_DELTA_PRESERVES_RX_BD_QUEUE_lemma = store_thm (
  "RX_NIC_DELTA_PRESERVES_RX_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC ``rx_bd_queue nic`` (GEN ``q : 32 word list`` (SPEC_ALL RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)))) THEN
  ASSUME_TAC (UNDISCH (SPECL [``(nic_delta : nic_delta_type) nic``, ``rx_bd_queue nic``] RX_BD_QUEUE_IMP_rx_bd_queue_lemma)) THEN
  ASM_REWRITE_TAC [NIC_DELTA_PRESERVES_RX_BD_QUEUE_def]);

val RX_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic q cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM (nic_delta nic) /\
    BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ¬BD_LIST_OVERLAP q /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic /\
    (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp) /\
    MEM nic.rx.current_bd_pa q /\
    ((nic_delta nic).rx.current_bd_pa = nic.rx.current_bd_pa)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC ``(nic_delta : nic_delta_type) nic`` RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_IMP_EQ_BD_QUEUE_lemma THEN

  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``nic.rx.sop_bd_pa``, ``((nic_delta : nic_delta_type) nic).rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``, ``((nic_delta : nic_delta_type) nic).regs.CPPI_RAM``, ``nic.rx.current_bd_pa``] BD_QUEUE_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN

  KEEP_ASM_RW_ASM_TAC ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp`` ``BD_QUEUE q' (read_ndp a m) m`` THEN
  ASM_RW_ASM_TAC ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp`` ``BD_QUEUE q' (read_ndp a m) m'`` THEN
  EXISTS_TAC ``q' : bd_pa_type list`` THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic`` NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def THEN
  ASM_REWRITE_TAC []);

val RX_SUBINVARIANT_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_SUBINVARIANT_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM (nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [GSYM NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def]);

val RX_NIC_DELTA_NEXT_STATE_FETCH_NEXT_BD_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_NIC_DELTA_NEXT_STATE_FETCH_NEXT_BD_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic q cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_FETCH_NEXT_BD (nic_delta nic) /\
    BD_QUEUE q nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    BDs_IN_CPPI_RAM q /\
    ¬BD_LIST_OVERLAP q /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    (read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp) /\
    MEM nic.rx.current_bd_pa q /\
    ((nic_delta nic).rx.current_bd_pa = nic.rx.current_bd.ndp)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC ``(nic_delta : nic_delta_type) nic`` RX_STATE_FETCH_NEXT_BD_IMP_unseen_bd_queue_EQ_bd_queue_CURRENT_BD_PA_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_IMP_EQ_BD_QUEUE_lemma THEN
  REFLECT_ASM_TAC ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM = nic.rx.current_bd.ndp`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC BD_QUEUE_EQ_START_BD_PA_MEM_IMP_START_NEXT_BD_QUEUE_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_NIC_DELTA_PRESERVES_BD_QUEUE_lemma)) THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_PRESERVES_RX_SOP_BD_PA_def THEN
  ASM_RW_ASM_TAC ``(nic_delta nic).rx.sop_bd_pa = nic.rx.sop_bd_pa`` ``BD_QUEUE q (nic_delta nic).rx.sop_bd_pa (nic_delta nic).regs.CPPI_RAM`` THEN
  EXISTS_TAC ``q : bd_pa_type list`` THEN
  EXISTS_TAC ``nic.rx.sop_bd_pa`` THEN
  ASM_REWRITE_TAC []);

val RX_SUBINVARIANT_NIC_DELTA_NEXT_STATE_FETCH_NEXT_BD_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "RX_SUBINVARIANT_NIC_DELTA_NEXT_STATE_FETCH_NEXT_BD_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_PRESERVES_RX_SOP_BD_PA nic_delta nic /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA nic_delta nic /\
    NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_FETCH_NEXT_BD (nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC RX_NIC_DELTA_NEXT_STATE_FETCH_NEXT_BD_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_bd_queue nic`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASM_REWRITE_TAC [GSYM RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  KEEP_ASM_RW_ASM_TAC ``RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic`` RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_lemma)) THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [GSYM NIC_DELTA_PRESERVES_RX_CURRENT_BD_PA_def] THEN
  RW_ASM_TAC ``NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP nic_delta nic`` NIC_DELTA_PRESERVES_RX_CURRENT_BD_NDP_def THEN
  RW_ASM_TAC ``NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA nic_delta nic`` NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_CURRENT_BD_PA_def THEN
  ASM_REWRITE_TAC []);





(* Start of lemmas for preservation of rx_unseen_bd_queue for transitions to write_cp. *)

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_RX_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_RX_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED q /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP q
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED q nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``  THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_EXISTS_BD_QUEUE_FOLLOWING_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_EXISTS_BD_QUEUE_FOLLOWING_CURRENT_BD_PA_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    ?q.
    BD_QUEUE (nic.rx.current_bd_pa::q) nic.rx.current_bd_pa nic.regs.CPPI_RAM /\
    BD_QUEUE q nic.rx.current_bd.ndp nic.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
  RW_KEEP_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``nic.rx.sop_bd_pa``, ``nic.rx.current_bd_pa``, ``nic.regs.CPPI_RAM``] BD_QUEUE_MEM_IMP_BD_QUEUE_SPLIT_lemma)) THEN
  REPEAT (PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm)) THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``rx_bd_queue nic = q' ++ [a] ++ q''`` (GSYM listTheory.APPEND_ASSOC) THEN
  RW_ASM_TAC ``rx_bd_queue nic = q' ++ ([a] ++ q'')`` listTheory.APPEND THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``q' : bd_pa_type list``, ``nic.rx.current_bd_pa``, ``q'' : bd_pa_type list``, ``nic.rx.sop_bd_pa``, ``nic.regs.CPPI_RAM``] MEMBER_OF_BD_QUEUE_IS_START_OF_SUBQUEUE_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA nic`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  PAT_ASSUM  ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  EXISTS_TAC ``q'' : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_BD_QUEUE_STRUCTURE_LOCATION_UNMODIFIED_IMP_UNSEEN_BD_QUEUE_LOCATION_UNMODIFIED_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_STRUCTURE_LOCATION_UNMODIFIED_IMP_UNSEEN_BD_QUEUE_LOCATION_UNMODIFIED_lemma",
  ``!nic CPPI_RAM.
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    BD_QUEUE_LOCATION_UNMODIFIED (rx_bd_queue nic) nic.regs.CPPI_RAM CPPI_RAM
    ==>
    BD_QUEUE_LOCATION_UNMODIFIED (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASM_RW_ASM_TAC ``x = y ++ z`` ``BD_QUEUE_LOCATION_UNMODIFIED q m m'`` THEN
  MATCH_MP_TAC BD_QUEUE_LOCATION_UNMODIFIED_IMP_SUFFIX_LOCATION_UNMODIFIED_lemma THEN
  EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);

val RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_CURRENT_BD_NDP_EQ_READ_NDP_CURRENT_BD_PA_lemma = store_thm (
  "RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_CURRENT_BD_NDP_EQ_READ_NDP_CURRENT_BD_PA_lemma",
  ``!nic.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    (nic.rx.current_bd.ndp = read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  REWRITE_TAC [RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH (SPEC_ALL thm))) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_ASSIGNS_CURRENT_BD_NDP_TO_SOP_BD_PA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic /\
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_STATE_WRITE_CP (nic_delta nic) /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)
    ==>
    NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE nic_delta nic``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_SUBINVARIANT_IMP_EXISTS_BD_QUEUE_FOLLOWING_CURRENT_BD_PA_lemma)) THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (GSYM (CONJ_ANT_TO_HYP (SPECL [``q : bd_pa_type list``, ``nic.rx.current_bd.ndp``, ``nic.regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma))) THEN
  ASSUME_TAC (GSYM (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_NEQ_idle_fetch_next_bd_write_cp_IMP_RX_UNSEEN_BD_QUEUE_EQ_BD_QUEUE_CURRENT_BD_NDP_lemma))) THEN
  ASM_RW_ASM_TAC ``bd_queue a m = rx_unseen_bd_queue nic`` ``q = bd_queue a m`` THEN
  ASM_RW_ASM_TAC ``q = rx_unseen_bd_queue nic`` ``BD_QUEUE (h::t) a m`` THEN
  RW_ASM_TAC ``BD_QUEUE (h::t) a m`` BD_QUEUE_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic_delta : nic_delta_type``, ``nic : nic_state``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``, ``rx_bd_queue nic``] NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_RX_SUBINVARIANT_IMP_BD_QUEUE_LOCATION_UNMODIFIED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``(nic_delta : nic_delta_type nic).regs.CPPI_RAM``] RX_INVARIANT_BD_QUEUE_STRUCTURE_LOCATION_UNMODIFIED_IMP_UNSEEN_BD_QUEUE_LOCATION_UNMODIFIED_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_unseen_bd_queue nic``, ``read_ndp nic.rx.current_bd_pa nic.regs.CPPI_RAM``, ``nic.regs.CPPI_RAM``, ``(nic_delta : nic_delta_type nic).regs.CPPI_RAM``] BD_QUEUE_LOCATION_UNMODIFIED_PRESERVES_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (GSYM (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_CURRENT_BD_NDP_EQ_READ_NDP_CURRENT_BD_PA_lemma))) THEN
  ASM_RW_ASM_TAC ``read_ndp a m = a'`` ``BD_QUEUE (rx_unseen_bd_queue nic) (read_ndp a m) m'`` THEN
  RW_ASM_TAC ``NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_RW_ASM_TAC ``x = y`` ``BD_QUEUE (rx_unseen_bd_queue nic) nic.rx.current_bd.ndp m`` THEN
  ASSUME_TAC (GSYM (UNDISCH (SPECL [``rx_unseen_bd_queue nic``, ``(nic_delta : nic_delta_type nic).rx.sop_bd_pa``, ``(nic_delta : nic_delta_type nic).regs.CPPI_RAM``] BD_QUEUE_IMP_bd_queue_lemma))) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_WRITE_CP_IMP_BD_QUEUE_EQ_RX_UNSEEN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(* End of lemmas for preservation of rx_unseen_bd_queue for transitions to write_cp. *)





(*****************************************************************)
(**End of preservation lemmas for reception transition functions**)
(*****************************************************************)


(**********************************************************************************************)
(**Start of lemmas for proving that sop_bd_pa, eop_bd_pa and current_bd_pa are in rx_bd_queue.*)
(**********************************************************************************************)

(*sop_bd_pa*)
val RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic cppi_ram_write_step_bd_pas.
    RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA nic cppi_ram_write_step_bd_pas /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_CURRENT_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_TRANS_lemma THEN
  EXISTS_TAC ``[nic.rx.current_bd_pa]`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
  MATCH_MP_TAC RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_MEM_CURRENT_BD_PA_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC []);

(*eop_bd_pa*)
val RX_STATE_WRITE_EOP_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_EOP_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic cppi_ram_write_step_bd_pas.
    RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_EOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_TRANS_lemma THEN
  EXISTS_TAC ``[nic.rx.eop_bd_pa]`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
  MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_EOP_OR_EOP_SOP_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma  THEN
  ASM_REWRITE_TAC [RX_STATE_WRITE_EOP_OR_EOP_SOP_def]);

(*eop_bd_pa and sop_bd_pa*)
val RX_STATE_WRITE_EOP_SOP_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_EOP_SOP_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic cppi_ram_write_step_bd_pas.
    RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_TRANS_lemma THEN
  EXISTS_TAC ``[nic.rx.eop_bd_pa;nic.rx.sop_bd_pa]`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC MEM2_LIST1_IMP_IN_LIST2_lemma THEN
  CONJ_TAC THENL
  [
   MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_EOP_OR_EOP_SOP_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC [RX_STATE_WRITE_EOP_OR_EOP_SOP_def]
   ,
   MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_STRUCTURE_SUPPORT_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC [RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_def, RX_STATE_WRITE_EOP_OR_EOP_SOP_def]
  ]);

val RX_STATE_SET_SOP_EOP_OVERRUN_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_SET_SOP_EOP_OVERRUN_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic cppi_ram_write_step_bd_pas.
    RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_CPPI_RAM_WRITE_EOP_SOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_EOP_SOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_TRANS_lemma THEN
  EXISTS_TAC ``[nic.rx.eop_bd_pa;nic.rx.sop_bd_pa]`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC MEM2_LIST1_IMP_IN_LIST2_lemma THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_OR_CLEAR_SOP_OWNER_AND_HDP_IMP_RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_lemma)) THEN
  CONJ_TAC THENL
  [
   MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_BD_STRUCTURE_SUPPORT_IMP_MEM_EOP_BD_PA_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC []
   ,
   MATCH_MP_TAC RX_STATE_WRITE_CPPI_RAM_POST_PROCESS_STRUCTURE_SUPPORT_IMP_MEM_SOP_BD_PA_BD_QUEUE_lemma THEN
   ASM_REWRITE_TAC []
  ]);

(*sop_bd_pa*)
val RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma",
  ``!nic cppi_ram_write_step_bd_pas.
    RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_SOP_BD_PA_def] THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC IN_LIST1_IMP_IN_LIST2_TRANS_lemma THEN
  EXISTS_TAC ``[nic.rx.sop_bd_pa]`` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC MEM_LIST1_IMP_IN_LIST2_lemma THEN
  MATCH_MP_TAC RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_FINITE_MEM_CURRENT_BD_PA_BD_QUEUE_IMP_MEM_SOP_BD_PA_RX_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_IMP_RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_lemma THEN
  ASM_REWRITE_TAC []);

val RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_WRITTEN_BDs_IN_RX_BD_QUEUE_lemma = store_thm (
  "RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_SUPPORT_IMP_WRITTEN_BDs_IN_RX_BD_QUEUE_lemma",
  ``!nic cppi_ram_write_step_bd_pas.
    RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA nic cppi_ram_write_step_bd_pas /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE cppi_ram_write_step_bd_pas (rx_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA nic cppi_ram_write_step_bd_pas`` RX_STATE_CPPI_RAM_WRITE_NOT_SOP_BD_PA_WRITE_CURRENT_SOP_OR_EOP_BD_PA_def THEN
  Cases_on `RX_STATE_WRITE_CURRENT_BD_PA_CPPI_RAM_WRITE_CURRENT_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_CURRENT_BD_PA_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_WRITE_EOP_CPPI_RAM_WRITE_EOP_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_EOP_RX_INVARIANT_BD_QUEUE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_WRITE_EOP_SOP_CPPI_RAM_WRITE_EOP_SOP_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_EOP_SOP_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  Cases_on `RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA nic cppi_ram_write_step_bd_pas` THENL
  [
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_WRITE_SOP_AND_NOT_WRITE_RX_SOP_BD_PA_CPPI_RAM_WRITE_SOP_BD_PA_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
   ASM_REWRITE_TAC []
   ,
   ASM_RW_ASM_TAC ``~P`` ``P \/ Q``
  ] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_SET_SOP_EOP_OVERRUN_RX_INVARIANT_BD_QUEUE_FINITE_STRUCTURE_IMP_WRITE_BD_IN_RX_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_NOT_RX_BD_QUEUE_EMPTY_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma = store_thm (
  "RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_NOT_RX_BD_QUEUE_EMPTY_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma",
  ``!nic.
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    ~RX_BD_QUEUE_EMPTY nic
    ==>
    MEM nic.rx.current_bd_pa (rx_bd_queue nic)``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [RX_STATE_WRITE_CP_NOT_BD_QUEUE_EMPTY_def] THEN
  REPEAT DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => MATCH_MP_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_SPLIT_RX_STATEs_lemma)) THEN
  REWRITE_TAC [RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_def] THEN
  REWRITE_TAC [GSYM boolTheory.DISJ_ASSOC] THEN
  RW_ASM_TAC ``P \/ Q`` RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_def THEN
  RW_ASM_TAC ``P \/ Q`` (GSYM boolTheory.DISJ_ASSOC) THEN
  ASM_REWRITE_TAC []);

(********************************************************************************************)
(**End of lemmas for proving that sop_bd_pa, eop_bd_pa and current_bd_pa are in rx_bd_queue.*)
(********************************************************************************************)

val RX_BD_QUEUE_EMPTY_IMP_RX_BD_QUEUE_EQ_EMPTY_lemma = store_thm (
  "RX_BD_QUEUE_EMPTY_IMP_RX_BD_QUEUE_EQ_EMPTY_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_BD_QUEUE_EMPTY nic
    ==>
    (rx_bd_queue nic = [])``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``x = y`` ``BD_QUEUE q a m`` THEN
  ASSUME_TAC (SPEC ``nic.regs.CPPI_RAM`` BD_QUEUE_EMPTY_START_ZERO_lemma) THEN
  MATCH_MP_TAC EQ_START_EQ_QUEUEs_lemma THEN
  EXISTS_TAC ``0w : 32 word`` THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  ASM_REWRITE_TAC []);

val RX_INVARIANT_WELL_DEFINED_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_NOT_RX_BD_QUEUE_EMPTY_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma = store_thm (
  "RX_INVARIANT_WELL_DEFINED_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_NOT_RX_BD_QUEUE_EMPTY_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma",
  ``!nic.
    RX_INVARIANT_WELL_DEFINED nic /\
    RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic /\
    ~RX_BD_QUEUE_EMPTY nic
    ==>
    rx_bd_queue nic <> []``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_AUTONOMOUS_TRANSITION_ENABLE_NOT_RX_BD_QUEUE_EMPTY_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
  Cases_on `rx_bd_queue nic` THENL
  [
   RW_ASM_TAC ``MEM nic.rx.current_bd_pa []`` listTheory.MEM THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   REWRITE_TAC [listTheory.NOT_CONS_NIL]
  ]);

val RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_BD_QUEUE_NEQ_EMPTY_lemma = store_thm (
  "RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_BD_QUEUE_NEQ_EMPTY_lemma",
  ``!nic.
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    rx_bd_queue nic <> []``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASM_RW_ASM_TAC ``RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic`` ``P ==> Q`` THEN
  Cases_on `rx_bd_queue nic` THENL
  [
   RW_ASM_TAC ``MEM e []`` listTheory.MEM THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   REWRITE_TAC [listTheory.NOT_CONS_NIL]
  ]);

val RX_INVARIANT_BD_QUEUE_FINITE_RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma = store_thm (
  "RX_INVARIANT_BD_QUEUE_FINITE_RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma",
  ``!nic.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE nic /\
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    ~RX_BD_QUEUE_EMPTY nic``,
  GEN_TAC THEN
  REWRITE_TAC [RX_BD_QUEUE_EMPTY_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_RX_BD_QUEUE_NEQ_EMPTY_lemma)) THEN
  Cases_on `nic.rx.sop_bd_pa = 0w` THENL
  [
   ASM_RW_ASM_TAC ``x = 0w`` ``BD_QUEUE q a m`` THEN
   ASSUME_TAC (SPEC ``nic.regs.CPPI_RAM`` BD_QUEUE_EMPTY_START_ZERO_lemma) THEN
   ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``rx_bd_queue nic``, ``[] : 32 word list``, ``0w : 32 word``, ``nic.regs.CPPI_RAM``] EQ_START_EQ_QUEUEs_lemma)) THEN
   ASM_RW_ASM_TAC ``rx_bd_queue nic = []`` ``rx_bd_queue nic <> []`` THEN
   UNDISCH_TAC ``F`` THEN
   REWRITE_TAC []
   ,
   ASM_REWRITE_TAC []
  ]);

val RX_INVARIANT_WELL_DEFINED_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma = store_thm (
  "RX_INVARIANT_WELL_DEFINED_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma",
  ``!nic.
    RX_INVARIANT_WELL_DEFINED nic /\
    RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM nic
    ==>
    ~RX_BD_QUEUE_EMPTY nic``,
  GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_WELL_DEFINED_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_INVARIANT_BD_QUEUE_FINITE_RX_INVARIANT_CURRENT_BD_PA_IN_BD_QUEUE_RX_STATE_FETCH_NEXT_BD_OR_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_NOT_RX_BD_QUEUE_EMPTY_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_SUBINVARIANT_MEM_IMP_PRESERVES_SUFFIX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_SUBINVARIANT_MEM_IMP_PRESERVES_SUFFIX_BD_QUEUE_lemma",
  ``!nic nic_delta bd_pa cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    MEM bd_pa (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic)
    ==>
    ?q' q''. (rx_bd_queue nic = (q' ++ [bd_pa]) ++ q'') /\ BD_QUEUE q'' (read_ndp bd_pa nic.regs.CPPI_RAM) (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_FINITE nic`` RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic)`` RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def THEN
  MATCH_MP_TAC NIC_DELTA_MEM_NON_OVERLAPPING_BD_QUEUE_IMP_PRESERVES_SUFFIX_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic.rx.sop_bd_pa`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_NOT_EXPAND_RX_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_NOT_EXPAND_RX_BD_QUEUE_lemma",
  ``!nic nic_delta bd_pa cppi_ram_write_step_bd_pas.
    RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM nic /\
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (rx_bd_queue nic) /\
    NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic
    ==>
    ?q. rx_bd_queue nic = q ++ (rx_bd_queue (nic_delta nic))``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL RX_STATE_ISSUE_NEXT_MEMORY_WRITE_REQUEST_OR_WRITE_CPPI_RAM_RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_IMP_MEM_RX_CURRENT_BD_PA_RX_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic : nic_state``, ``nic_delta : nic_delta_type``, ``nic.rx.current_bd_pa``, ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``] NIC_DELTA_SUBINVARIANT_MEM_IMP_PRESERVES_SUFFIX_BD_QUEUE_lemma)) THEN
  REPEAT (PAT_ASSUM ``?x : bd_pa_type list. P`` (fn thm => CHOOSE_TAC thm)) THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT nic`` RX_INVARIANT_BD_QUEUE_STRUCTURE_SUPPORT_def THEN
  RW_ASM_TAC ``P /\ Q`` RX_INVARIANT_STATE_ISSUE_MEMORY_REQUEST_OR_WRITE_CPPI_RAM_IMP_CURRENT_BD_NDP_EQ_NDP_CURRENT_BD_PA_def THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (GSYM (UNDISCH thm))) THEN
  ASM_RW_ASM_TAC ``read_ndp a m = p`` ``BD_QUEUE q a m`` THEN
  RW_ASM_TAC ``NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA nic_delta nic`` NIC_DELTA_ASSIGNS_CURRENT_BD_NDP_TO_RX_SOP_BD_PA_def THEN
  REFLECT_ASM_TAC ``(nic_delta nic).rx.sop_bd_pa = nic.rx.current_bd.ndp`` THEN
  ASM_RW_ASM_TAC ``nic.rx.current_bd.ndp = (nic_delta nic).rx.sop_bd_pa`` ``BD_QUEUE q a m`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (GSYM (SPECL [``nic_delta : nic_delta_type nic``, ``q'' : bd_pa_type list``] RX_BD_QUEUE_IMP_rx_bd_queue_lemma))) THEN
  ASM_RW_ASM_TAC ``q'' = rx_bd_queue (nic_delta nic)`` ``rx_bd_queue nic = q' ++ [nic.rx.current_bd_pa] ++ q''`` THEN
  EXISTS_TAC ``q' ++ [nic.rx.current_bd_pa] : bd_pa_type list`` THEN
  ASM_REWRITE_TAC []);
























val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def = Define `
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas =
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (MAP SND cppi_ram_write_step_bd_pas) /\
    BD_PAs_IN_RX_SEEN_BD_QUEUE (MAP SND cppi_ram_write_step_bd_pas) nic`;

val RX_BD_QUEUE_STRUCTURE_BD_PAs_IN_RX_SEEN_BD_QUEUE_IMP_BD_PAs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_STRUCTURE_BD_PAs_IN_RX_SEEN_BD_QUEUE_IMP_BD_PAs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic bd_pas rx_seen_bd_queue.
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic) /\
    BD_PAs_IN_RX_SEEN_BD_QUEUE bd_pas nic
    ==>
    IN_LIST1_IMP_IN_LIST2 bd_pas rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [BD_PAs_IN_RX_SEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [BD_PAs_IN_RX_BD_QUEUE_def, NOT_BD_PAs_IN_RX_UNSEEN_BD_QUEUE_def] THEN
  REWRITE_TAC [listTheory.EVERY_MEM] THEN
  BETA_TAC THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_def] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (UNDISCH (SPEC ``bd_pa : bd_pa_type`` thm))) THEN
  ASM_RW_ASM_TAC ``x = y ++ z`` ``MEM bd_pa (rx_bd_queue nic)`` THEN
  RW_ASM_TAC ``MEM bd_pa (x ++ y)`` listTheory.MEM_APPEND THEN
  ASM_RW_ASM_TAC ``~P`` ``P \/ Q`` THEN
  ASM_REWRITE_TAC []);

val RX_BD_QUEUE_STRUCTURE_NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "RX_BD_QUEUE_STRUCTURE_NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue nic_delta cppi_ram_write_step_bd_pas.
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas
    ==>
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC RX_BD_QUEUE_STRUCTURE_BD_PAs_IN_RX_SEEN_BD_QUEUE_IMP_BD_PAs_IN_RX_SEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  ASM_REWRITE_TAC []);

val CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_TRANS_lemma = store_thm (
  "CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_TRANS_lemma",
  ``!q1 q2 q3.
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE q1 q2 /\
    IN_LIST1_IMP_IN_LIST2 q2 q3
    ==>
    CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE q1 q3``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_def] THEN
  REWRITE_TAC [IN_LIST1_IMP_IN_LIST2_TRANS_lemma]);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_TRANS_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_TRANS_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas q.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas (MAP SND cppi_ram_write_step_bd_pas) /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) q
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas q``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type``, ``MAP SND (cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type)``, ``q : bd_pa_type list``] CPPI_RAM_WRITE_STEPs_WRITE_BDs_IN_BD_QUEUE_TRANS_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas rx_seen_bd_queue.
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas /\
    IN_LIST1_IMP_IN_LIST2 (MAP SND cppi_ram_write_step_bd_pas) rx_seen_bd_queue
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_def] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_TRANS_lemma THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_WRITES_SEEN_BDs_lemma = store_thm (
  "NIC_DELTA_WRITES_SEEN_BDs_lemma",
  ``!nic rx_seen_bd_queue nic_delta cppi_ram_write_step_bd_pas.
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas
    ==>
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas rx_seen_bd_queue``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC RX_BD_QUEUE_STRUCTURE_NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``nic_delta : nic_delta_type`` THEN
  ASM_REWRITE_TAC []); 

val SEEN_UNSEEN_RX_BDs_NO_OVERLAP_lemma = store_thm (
  "SEEN_UNSEEN_RX_BDs_NO_OVERLAP_lemma",
  ``!nic_delta nic cppi_ram_write_step_bd_pas rx_seen_bd_queue.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic)
    ==>
    NO_BD_LIST_OVERLAP rx_seen_bd_queue (rx_unseen_bd_queue nic)``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  MATCH_MP_TAC BD_QUEUE_NOT_BD_LIST_OVERLAP_IMP_NO_BD_SPLIT_OVERLAP_lemma THEN
  EXISTS_TAC ``nic.rx.sop_bd_pa`` THEN
  EXISTS_TAC ``nic.regs.CPPI_RAM`` THEN
  SPLIT_ASM_TAC THEN
  REFLECT_ASM_TAC ``x = y`` THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma = store_thm (
  "NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma",
  ``!nic rx_seen_bd_queue nic_delta cppi_ram_write_step_bd_pas.
    BD_QUEUE (rx_bd_queue nic) nic.rx.sop_bd_pa nic.regs.CPPI_RAM /\
    (rx_bd_queue nic = rx_seen_bd_queue ++ rx_unseen_bd_queue nic) /\
    ~BD_LIST_OVERLAP (rx_bd_queue nic) /\
    BDs_IN_CPPI_RAM (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas rx_seen_bd_queue
    ==>
    EQ_BDs (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_BD_QUEUE_NON_OVERLAPPING_BD_QUEUEs_IN_CPPI_RAM_IMP_PRESERVED_NON_OVERLAPPING_BD_QUEUE_lemma THEN
  EXISTS_TAC ``rx_seen_bd_queue : bd_pa_type list`` THEN
  EXISTS_TAC ``cppi_ram_write_step_bd_pas : cppi_ram_write_step_bd_pas_type`` THEN
  KEEP_ASM_RW_ASM_TAC ``x = y`` ``BDs_IN_CPPI_RAM q`` THEN
  ASSUME_TAC (UNDISCH (SPECL [``rx_seen_bd_queue : bd_pa_type list``, ``rx_unseen_bd_queue nic``] BDs_IN_CPPI_RAM_IMP_SPLITs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL SEEN_UNSEEN_RX_BDs_NO_OVERLAP_lemma)) THEN
  ASM_REWRITE_TAC []);

val NIC_DELTA_RX_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma = store_thm (
  "NIC_DELTA_RX_SUBINVARIANT_IMP_RX_UNSEEN_BD_QUEUE_PRESERVED_lemma",
  ``!nic nic_delta cppi_ram_write_step_bd_pas.
    RX_INVARIANT_BD_QUEUE_FINITE nic /\
    RX_INVARIANT_BD_QUEUE_STRUCTURE nic /\
    RX_INVARIANT_BD_QUEUE_NO_OVERLAP (rx_bd_queue nic) /\
    RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED (rx_bd_queue nic) /\
    NIC_DELTA_WRITES_FIELDs_NOT_NDP_OF_BDs_IN_RX_SEEN_BD_QUEUE nic_delta nic cppi_ram_write_step_bd_pas
    ==>
    EQ_BDs (rx_unseen_bd_queue nic) nic.regs.CPPI_RAM (nic_delta nic).regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_FINITE_EQ_BD_QUEUE_RX_BD_QUEUE_lemma] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_STRUCTURE_def] THEN
  REWRITE_TAC [RX_INVARIANT_BD_QUEUE_NO_OVERLAP_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  PAT_ASSUM ``?x.P`` (fn thm => CHOOSE_TAC thm) THEN
  ASSUME_TAC (UNDISCH (SPEC ``rx_bd_queue nic`` RX_INVARIANT_BD_QUEUE_LOCATION_DEFINED_IMP_BDs_IN_CPPI_RAM_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_WRITES_SEEN_BDs_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL NIC_DELTA_PRESERVES_RX_UNSEEN_BD_QUEUE_lemma)) THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

