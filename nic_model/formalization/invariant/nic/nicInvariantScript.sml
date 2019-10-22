open HolKernel Parse boolLib bossLib;
open stateTheory;
open qdInvariantTheory;
open itInvariantTheory;
open txInvariantTheory;
open rxInvariantTheory;
open tdInvariantTheory;
open rdInvariantTheory;

val _ = new_theory "nicInvariant";

val NIC_STATE_DEFINED_def = Define `
  NIC_STATE_DEFINED nic = ~nic.dead`;

(* This is the invariant of the NIC that implies that the NIC never enters an
   undefined state, and if the NIC issues a memory request then the address of
   that request is in READABLE or WRITABLE depending on whether it is a read or
   write request. *)
val NIC_INVARIANT_def = Define `
  NIC_INVARIANT nic READABLE WRITABLE =
  NIC_STATE_DEFINED nic /\
  QD_INVARIANT nic /\
  IT_INVARIANT nic /\
  TX_INVARIANT nic READABLE /\
  RX_INVARIANT nic WRITABLE /\
  TD_INVARIANT nic /\
  RD_INVARIANT nic`;

val _ = export_theory();

