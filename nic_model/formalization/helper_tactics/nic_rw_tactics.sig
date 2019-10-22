signature nic_rw_tactics =
sig

  (*
   * Given a term quatoation `state_name`, rewrites state_name to (<some state>_state b b0 n i t t0 r r0)
   *)
  val rw_state_tactic : Abbrev.term quotation -> Thm.thm list -> Abbrev.tactic;

end
