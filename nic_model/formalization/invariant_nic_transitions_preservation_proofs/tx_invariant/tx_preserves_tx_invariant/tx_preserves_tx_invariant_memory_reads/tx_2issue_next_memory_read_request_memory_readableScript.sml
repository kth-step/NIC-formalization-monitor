open HolKernel Parse boolLib bossLib;
open helperTactics;
open tx_2issue_next_memory_read_request_lemmasTheory;
open tx_bd_queueTheory;
open txInvariantMemoryReadsTheory;
open tx_state_definitionsTheory;
open tx_state_lemmasTheory;
open txInvariantTheory;

val _ = new_theory "tx_2issue_next_memory_read_request_memory_readable";

val TX_issue_next_memory_read_request_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma = prove (
  ``!nic nic' mr' READABLE.
    ((nic', mr') = tx_2issue_next_memory_read_request nic) /\
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic) READABLE nic.regs.CPPI_RAM
    ==>
    TX_INVARIANT_MEMORY_READABLE_BD_QUEUE (tx_bd_queue nic') READABLE nic'.regs.CPPI_RAM``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_issue_next_memory_read_request_NON_MODIFICATION_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL EQ_SOP_BD_PA_AND_CPPI_RAM_AND_TX_INVARIANT_BD_QUEUE_FINITE_IMP_EQ_BD_QUEUES_lemma)) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_issue_next_memory_read_request_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma = prove (
  ``!nic nic' mr'.
    ((nic', mr') = tx_2issue_next_memory_read_request nic) /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_issue_next_memory_read_request_NEXT_STATE_NEQ_issue_next_memory_read_request_lemma)) THEN
  ASM_REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def]);




(******************************************************************************)



val TX_issue_next_memory_read_request_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma = prove (
  ``!nic nic' mr'.
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic /\
    ((nic', mr') = tx_2issue_next_memory_read_request nic) /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic
    ==>
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic'``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_issue_next_memory_read_request_PRESERVES_PA_MEMORY_REQUEST_PLUS_BYTES_LEFT_TO_REQUEST_lemma)) THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def] THEN
  ASM_REWRITE_TAC [] THEN
  WEAKEN_TAC is_conj THEN
  WEAKEN_TAC is_eq THEN
  DISCH_TAC THEN
  WEAKEN_TAC is_disj THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic`` TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def THEN
  KEEP_ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic`` TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``P ==> Q`` (fn thm => ASSUME_TAC (UNDISCH thm)) THEN
  ASSUME_TAC (UNDISCH (SPECL [``nic.tx.pa_of_next_memory_buffer_byte``, ``nic.tx.number_of_buffer_bytes_left_to_request - 1w``] (blastLib.BBLAST_PROVE ``!(s : 32 word) (l : 32 word). ~(s + l <+ s) ==> l >+ 0w ==> ~((s + 1w) + (l - 1w) <+ s + 1w )``))) THEN
  ASM_REWRITE_TAC []);



(******************************************************************************)



val TX_issue_next_memory_read_request_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma = prove (
  ``!nic nic' mr' READABLE.
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic /\
    ((nic', mr') = tx_2issue_next_memory_read_request nic) /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic /\
    TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic /\
    TX_INVARIANT_MEMORY_READABLE_STATE nic READABLE
    ==>
    TX_INVARIANT_MEMORY_READABLE_STATE nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_STATE_def] THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_issue_next_memory_read_request_NEXT_STATE_EQ_process_memory_read_reply_lemma)) THEN
  RW_ASM_TAC ``P \/ Q`` TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST_def THEN
  RW_ASM_TAC ``P \/ Q`` TX_STATE_PROCESS_MEMORY_READ_REPLY_def THEN
  ASSUME_TAC (UNDISCH (SPEC ``nic' : nic_state`` TX_STATE_PROCESS_MEMORY_READ_REPLY_IMP_tx_process_memory_read_reply_lemma)) THEN
  ASM_RW_ASM_TAC ``nic'.tx.state = tx_process_memory_read_reply`` ``P \/ Q`` THEN
  RW_ASM_TAC ``P \/ Q`` (GSYM stateTheory.tx_abstract_state_distinct) THEN
  GEN_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC_ALL TX_issue_next_memory_read_request_PRESERVES_PA_MEMORY_REQUEST_PLUS_BYTES_LEFT_TO_REQUEST_lemma)) THEN
  ASM_REWRITE_TAC [] THEN
  ASM_RW_ASM_TAC ``P /\ Q`` ``nic'.tx.number_of_buffer_bytes_left_to_request >+ 0w`` THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE_STATE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_STATE_def THEN
  KEEP_ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (SPEC ``pa : 32 word`` thm)) THEN
  RW_ASM_TAC ``pa <=+ nic.tx.pa_of_next_memory_buffer_byte + 1w + (nic.tx.number_of_buffer_bytes_left_to_request − 1w - 1w)`` (blastLib.BBLAST_PROVE ``!(x : 32 word) (y : 32 word). x + 1w + (y - 1w - 1w) = x + (y - 1w)``) THEN
  KEEP_ASM_RW_ASM_TAC ``pa <=+ nic.tx.pa_of_next_memory_buffer_byte + (nic.tx.number_of_buffer_bytes_left_to_request - 1w)`` ``P ==> Q`` THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic`` TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def THEN
  KEEP_ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P ==> Q`` THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE nic`` TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P ==> Q`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic.tx.number_of_buffer_bytes_left_to_request >+ 0w`` ``P ==> Q`` THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPECL [``nic.tx.pa_of_next_memory_buffer_byte``, ``nic.tx.number_of_buffer_bytes_left_to_request - 1w``, ``pa : 32 word``] (blastLib.BBLAST_PROVE ``!(s : 32 word) l pa. l >+ 0w /\ ~(s + l <+ s) /\ s + 1w <=+ pa /\ pa <=+ s + l ==> s <=+ pa``))) THEN
  ASM_RW_ASM_TAC ``nic.tx.pa_of_next_memory_buffer_byte ≤₊ pa`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);




(******************************************************************************)






(* Preservation of the complete invariant of the transmission automaton. *)
val TX_issue_next_memory_read_request_PRESERVES_TX_INVARIANT_MEMORY_lemma = store_thm (
  "TX_issue_next_memory_read_request_PRESERVES_TX_INVARIANT_MEMORY_lemma",
  ``!nic nic' mr' READABLE.
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic /\
    ((nic', mr') = tx_2issue_next_memory_read_request nic) /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    TX_INVARIANT_MEMORY nic' READABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_def] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL tx_2issue_next_memory_read_requestTheory.TX_issue_next_memory_read_request_PRESERVES_TX_INVARIANT_WELL_DEFINED_lemma)) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_READABLE nic READABLE`` TX_INVARIANT_MEMORY_READABLE_def THEN
  SPLIT_ASM_TAC THEN
  REWRITE_TAC [TX_INVARIANT_MEMORY_READABLE_def] THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_issue_next_memory_read_request_PRESERVES_MEMORY_READABLE_BD_QUEUE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_issue_next_memory_read_request_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_lemma)) THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_issue_next_memory_read_request_PRESERVES_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_lemma)) THEN
  ASSUME_TAC(CONJ_ANT_TO_HYP (SPEC_ALL TX_issue_next_memory_read_request_IMP_NEXT_STATE_MEMORY_READABLE_STATE_lemma)) THEN
  ASM_REWRITE_TAC []);






(**************PROOF OF MEMORY REQUESTS ACCESSING ONLY READABLE MEMORY*********)



(* The transmission automaton issues only memory accesses that are allowed to be read. *)
val TX_issue_next_memory_read_request_ISSUES_READABLE_PAs_lemma = store_thm (
  "TX_issue_next_memory_read_request_ISSUES_READABLE_PAs_lemma",
  ``!nic nic' mr' READABLE.
    ((nic', mr') = tx_2issue_next_memory_read_request nic) /\
    TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic /\
    TX_INVARIANT_MEMORY nic READABLE
    ==>
    IS_SOME mr' /\
    READABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  ASSUME_TAC (CONJ_ANT_TO_HYP (SPEC_ALL TX_issue_next_memory_read_request_PA_lemma)) THEN
  SPLIT_ASM_TAC THEN
  ASM_REWRITE_TAC [] THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY nic READABLE`` TX_INVARIANT_MEMORY_def THEN
  RW_ASM_TAC ``P /\ Q`` TX_INVARIANT_MEMORY_READABLE_def THEN
  RW_ASM_TAC ``P /\ Q`` TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_STATE_def THEN
  RW_ASM_TAC ``P /\ Q`` TX_INVARIANT_MEMORY_READABLE_STATE_def THEN
  SPLIT_ASM_TAC THEN
  KEEP_ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic ==> P`` THEN
  KEEP_ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P ==> Q`` THEN
  PAT_ASSUM ``!x.P`` (fn thm => ASSUME_TAC (REWRITE_RULE [wordsTheory.WORD_LOWER_EQ_REFL] (SPEC ``nic.tx.pa_of_next_memory_buffer_byte`` thm))) THEN
  RW_ASM_TAC ``TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE nic`` TX_INVARIANT_MEMORY_BYTES_LEFT_TO_REQUEST_IMP_NO_OVERFLOW_STATE_def THEN
  ASM_RW_ASM_TAC ``TX_STATE_ISSUE_NEXT_MEMORY_READ_REQUEST nic`` ``P \/ Q ==> R`` THEN
  KEEP_ASM_RW_ASM_TAC ``nic.tx.number_of_buffer_bytes_left_to_request >+ 0w`` ``nic.tx.number_of_buffer_bytes_left_to_request >+ 0w ==> P`` THEN
  RW_ASM_TAC ``~P`` wordsTheory.WORD_NOT_LOWER THEN
  ASM_RW_ASM_TAC ``nic.tx.pa_of_next_memory_buffer_byte <=+ nic.tx.pa_of_next_memory_buffer_byte + (nic.tx.number_of_buffer_bytes_left_to_request − 1w)`` ``P ==> Q`` THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

