structure nic_rw_tactics :> nic_rw_tactics =
struct

  open HolKernel Parse boolLib bossLib;

  fun rw_state_tactic state_name lemmas =
     Cases_on state_name THEN
     REWRITE_TAC lemmas;

end
