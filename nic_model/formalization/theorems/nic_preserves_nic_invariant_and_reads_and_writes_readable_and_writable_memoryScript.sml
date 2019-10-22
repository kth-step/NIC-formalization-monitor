open HolKernel Parse boolLib bossLib;
open helperTactics;
open nic_modelTheory;
open nicInvariantTheory;
open nic_preserves_nic_invariantTheory;
open nic_transition_definitionsTheory;
open address_spaceTheory;
open stateTheory;
open tx_state_definitionsTheory;

val _ = new_theory "nic_preserves_nic_invariant_and_reads_and_writes_readable_and_writable_memory";

(* NIC register read transitions preserve the NIC invariant. *)
val NIC_REGISTER_READS_PRESERVE_NIC_INVARIANT_thm = store_thm (
  "NIC_REGISTER_READS_PRESERVE_NIC_INVARIANT_thm",
  ``!nic env pa nic' value' READABLE WRITABLE.
    ((nic', value') = nic_transition_register_read env pa nic) /\
    ((1 -- 0) pa = 0w) /\               (* Assume register address is word aligned. *)
    NIC_INVARIANT nic READABLE WRITABLE
    ==>
    NIC_INVARIANT nic' READABLE WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_REGISTER_READ_TRANSITION_PRESERVES_NIC_INVARIANT_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  EXISTS_TAC ``pa : 32 word`` THEN
  EXISTS_TAC ``value' : 32 word`` THEN
  REWRITE_TAC [NIC_REGISTER_READ_TRANSITION_def] THEN
  REWRITE_TAC [WORD32_ALIGNED_def] THEN
  ASM_REWRITE_TAC []);

(* Autonomous NIC transitions preserve the NIC invariant. *)
val NIC_AUTONOMOUS_TRANSITIONS_PRESERVE_NIC_INVARIANT_thm = store_thm (
  "NIC_AUTONOMOUS_TRANSITIONS_PRESERVE_NIC_INVARIANT_thm",
  ``!nic env nic' mr' int' READABLE WRITABLE.
    ((nic', mr', int') = nic_transition_autonomous env nic) /\
    NIC_INVARIANT nic READABLE WRITABLE
    ==>
    NIC_INVARIANT nic' READABLE WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_AUTONOMOUS_TRANSITION_PRESERVES_NIC_INVARIANT_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN  
  EXISTS_TAC ``mr' : memory_request option`` THEN
  EXISTS_TAC ``int' : bool`` THEN
  REWRITE_TAC [NIC_AUTONOMOUS_TRANSITION_def] THEN
  ASM_REWRITE_TAC []);

(* Memory read reply transitions of the NIC preserve the NIC invariant. *)
val NIC_PROCESS_MEMORY_READ_REPLY_TRANSITIONS_PRESERVE_NIC_INVARIANT_thm = store_thm (
  "NIC_PROCESS_MEMORY_READ_REPLY_TRANSITIONS_PRESERVE_NIC_INVARIANT_thm",
  ``!nic mr nic' READABLE WRITABLE.
    (nic' = nic_transition_memory_read_reply mr nic) /\
    (nic.tx.state = tx_process_memory_read_reply) /\
    NIC_INVARIANT nic READABLE WRITABLE
    ==>
    NIC_INVARIANT nic' READABLE WRITABLE``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_MEMORY_READ_REPLY_TRANSITION_PRESERVES_NIC_INVARIANT_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``mr : memory_request`` THEN
  REWRITE_TAC [NIC_MEMORY_READ_REPLY_TRANSITION_def] THEN
  REWRITE_TAC [TX_STATE_PROCESS_MEMORY_READ_REPLY_def] THEN
  ASM_REWRITE_TAC []);

(* Autonomous NIC transitions issuing memory read requests address only readable memory. *)
val NIC_AUTONOMOUS_TRANSITIONS_READ_READABLE_MEMORY_thm = store_thm (
  "NIC_AUTONOMOUS_TRANSITIONS_READ_READABLE_MEMORY_thm",
  ``!nic env nic' mr' int' READABLE WRITABLE.
    ((nic', mr', int') = nic_transition_autonomous env nic) /\
    NIC_INVARIANT nic READABLE WRITABLE /\
    IS_SOME mr' /\          (* Memory request. *)
    IS_NONE (THE mr').v     (* Read request. *)
    ==>
    READABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_AUTONOMOUS_TRANSITION_READS_READABLE_MEMORY_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  EXISTS_TAC ``nic' : nic_state`` THEN
  EXISTS_TAC ``int' : bool`` THEN
  EXISTS_TAC ``WRITABLE : 32 word -> bool`` THEN
  REWRITE_TAC [NIC_AUTONOMOUS_TRANSITION_def] THEN
  ASM_REWRITE_TAC []);

(* Autonomous NIC transitions issuing memory write requests address only writable memory. *)
val NIC_AUTONOMOUS_TRANSITIONS_WRITE_WRITABLE_MEMORY_thm = store_thm (
  "NIC_AUTONOMOUS_TRANSITIONS_WRITE_WRITABLE_MEMORY_thm",
  ``!nic env nic' mr' int' READABLE WRITABLE.
    ((nic', mr', int') = nic_transition_autonomous env nic) /\
    NIC_INVARIANT nic READABLE WRITABLE /\
    IS_SOME mr' /\          (* Memory request. *)
    IS_SOME (THE mr').v     (* Write request. *)
    ==>
    WRITABLE (THE mr').pa``,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPLIT_ASM_TAC THEN
  MATCH_MP_TAC NIC_AUTONOMOUS_TRANSITION_WRITES_WRITABLE_MEMORY_lemma THEN
  EXISTS_TAC ``nic : nic_state`` THEN
  EXISTS_TAC ``env : environment`` THEN
  EXISTS_TAC ``nic' : nic_state`` THEN
  EXISTS_TAC ``int' : bool`` THEN
  EXISTS_TAC ``READABLE : 32 word -> bool`` THEN
  REWRITE_TAC [NIC_AUTONOMOUS_TRANSITION_def] THEN
  ASM_REWRITE_TAC []);

val _ = export_theory();

