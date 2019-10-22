open HolKernel Parse boolLib bossLib;
open rxInvariantWellDefinedTheory;
open rxInvariantMemoryWritesTheory;

val _ = new_theory "rxInvariant";

(******************************************************************************)
(******************************************************************************)
(*Final invariant of the reception automaton implying that the NIC can only****)
(*write writable memory.*******************************************************)
(******************************************************************************)
(******************************************************************************)
val RX_INVARIANT_MEMORY_def = Define `
  RX_INVARIANT_MEMORY nic WRITABLE =
  RX_INVARIANT_WELL_DEFINED nic /\
  RX_INVARIANT_MEMORY_WRITABLE nic WRITABLE`;

(******************************************************************************)
(* Final invariant of the reception automaton when combined with the          *)
(* invariants of the other automata.                                          *)
(******************************************************************************)
val RX_INVARIANT_def = Define `
  RX_INVARIANT nic WRITABLE =
  RX_STATE_AUTONOMOUS_TRANSITION_ENABLE nic
  ==>
  RX_INVARIANT_MEMORY nic WRITABLE`;

val _ = export_theory();

