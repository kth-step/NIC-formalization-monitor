open HolKernel Parse boolLib bossLib;
open stateTheory;
open wordsTheory;
open address_spaceTheory;
open CPPI_RAMTheory;

val _ = new_theory "register_read";

val read_register_def = Define `
  read_register (env : environment) (pa : 32 word) (nic : nic_state) =
  if nic.dead then
    (nic, env.reg_read)
  else if ~WORD32_ALIGNED pa then
    (nic with dead := T, env.reg_read)
  else if pa = TX_TEARDOWN_PA then
    (nic, w2w nic.regs.TX_TEARDOWN)
  else if pa = RX_TEARDOWN_PA then
    (nic, w2w nic.regs.RX_TEARDOWN)
  else if pa = CPDMA_SOFT_RESET_PA then
    (nic, w2w nic.regs.CPDMA_SOFT_RESET)
  else if pa = DMACONTROL_PA then
    (nic, w2w nic.regs.DMACONTROL)
  else if pa = RX_BUFFER_OFFSET_PA then
    (nic, w2w nic.regs.RX_BUFFER_OFFSET)
  else if pa = TX0_HDP_PA then
    (nic, nic.regs.TX0_HDP)
  else if pa = RX0_HDP_PA then
    (nic, nic.regs.RX0_HDP)
  else if pa = TX0_CP_PA then
    (nic, nic.regs.TX0_CP)
  else if pa = RX0_CP_PA then
    (nic, nic.regs.RX0_CP)
  (* pa is word aligned by the second check above. Therefore pa will address
     only CPPI_RAM if this check is passed. *)
  else if CPPI_RAM_BYTE_PA pa then
    (nic, read_bd_word pa 0w nic.regs.CPPI_RAM)
  else
    (nic, env.reg_read)`;

val _ = export_theory();

