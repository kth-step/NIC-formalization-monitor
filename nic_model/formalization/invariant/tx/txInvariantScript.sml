open HolKernel Parse boolLib bossLib;
open txInvariantWellDefinedTheory;
open txInvariantMemoryReadsTheory;
open tx_transition_definitionsTheory;

val _ = new_theory "txInvariant";

(******************************************************************************)
(*Final invariant of the transmission automaton implying that the transmission*)
(*part of the NIC can only address readable memory (and not not perform********)
(*undefined actions).**********************************************************)
(******************************************************************************)
val TX_INVARIANT_MEMORY_def = Define `
  TX_INVARIANT_MEMORY nic READABLE =
  TX_INVARIANT_WELL_DEFINED nic /\
  TX_INVARIANT_MEMORY_READABLE nic READABLE`;

(******************************************************************************)
(* Final invariant of the transmission automaton when combined with the       *)
(* invariants of the other automata.                                          *)
(******************************************************************************)
val TX_INVARIANT_def = Define `
  TX_INVARIANT nic READABLE =
  TX_STATE_AUTONOMOUS_TRANSITION_ENABLE_OR_PROCESS_MEMORY_READ_REPLY nic
  ==>
  TX_INVARIANT_MEMORY nic READABLE`;

val _ = export_theory();

