open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory "address_space";

(*
 * True if and only if pa is 32-bit word aligned. 1 -- 0 extracts bits at
 * positions 1 and 0 and returns a 32-bit word.
 *)
val WORD32_ALIGNED_def = Define `
  WORD32_ALIGNED (pa : 32 word) = ((1 -- 0) pa = 0w)`;

(*
 * Physical start address of RAM on BeagleBone Black. Defined here due to lack
 * of other place (must be accessible to both transmission and reception).
 *)
val BBB_RAM_START_def = Define `BBB_RAM_START = 0x80000000w : 32 word`;

(*
 * Physical (exclusive) end address of RAM on BeagleBone Black. Defined here due
 * to lack of other place (must be accessible to both transmission and
 * reception).
 *)
val BBB_RAM_END_def = Define `BBB_RAM_END = 0xA0000000w : 32 word`;

(*
 * Physical inclusive start address of CPPI_RAM on BeagleBone Black.
 *)
val CPPI_RAM_START_def = Define `CPPI_RAM_START = 0x4A102000w : 32 word`;

(*
 * Physical exclusive end address of CPPI_RAM on BeagleBone Black.
 *)
val CPPI_RAM_END_def = Define `CPPI_RAM_END = 0x4A104000w : 32 word`;

(*
 * Physical inclusive start address of CPDMA_STATERAM on BeagleBone Black.
 *)
val CPDMA_STATERAM_START_def = Define `CPDMA_STATERAM_START = 0x4A10_0A00w : 32 word`;

(*
 * Offset of the TX0_HDP register relative the start address of CPDMA_STATERAM
 * on BeagleBone Black.
 *)
val TX_HDP_START_OFFSET_def = Define `TX_HDP_START_OFFSET = 0x0w : 32 word`;

(*
 * Offset of the TX7_HDP register relative the start address of CPDMA_STATERAM
 * on BeagleBone Black.
 *)
val TX_HDP_END_OFFSET_def = Define `TX_HDP_END_OFFSET = 0x1Cw : 32 word`;

(*
 * True if and only if pa addresses a byte of a TX[i]_HDP register, 1 <= i <= 7.
 *)
val TX1_7_HDP_BYTE_def = Define `
  TX1_7_HDP_BYTE pa =
  CPDMA_STATERAM_START + TX_HDP_START_OFFSET + 4w <=+ pa /\
  pa <+ CPDMA_STATERAM_START + TX_HDP_END_OFFSET + 4w`;

(*
 * Offset of the RX0_HDP register relative the start address of CPDMA_STATERAM
 * on BeagleBone Black.
 *)
val RX_HDP_START_OFFSET_def = Define `RX_HDP_START_OFFSET = 0x20w : 32 word`;

(*
 * Offset of the RX7_HDP register relative the start address of CPDMA_STATERAM
 * on BeagleBone Black.
 *)
val RX_HDP_END_OFFSET_def = Define `RX_HDP_END_OFFSET = 0x3Cw : 32 word`;

(*
 * True if and only if pa addresses a byte of a RX[i]_HDP register, 1 <= i <= 7.
 *)
val RX1_7_HDP_BYTE_def = Define `
  RX1_7_HDP_BYTE pa =
  CPDMA_STATERAM_START + RX_HDP_START_OFFSET + 4w <=+ pa /\
  pa <+ CPDMA_STATERAM_START + RX_HDP_END_OFFSET + 4w`;

(*
 * True if and only if pa addresses a byte of a TX[i]_HDP or RX[i]_HDP register,
 * 1 <= i <= 7.
 *)
val NOT_ZERO_CHANNEL_HDP_BYTE_def = Define `
  NOT_ZERO_CHANNEL_HDP_BYTE pa = TX1_7_HDP_BYTE pa \/ RX1_7_HDP_BYTE pa`;

val TX_TEARDOWN_PA_def = Define `TX_TEARDOWN_PA = 0x4A10_0808w : 32 word`;
val RX_TEARDOWN_PA_def = Define `RX_TEARDOWN_PA = 0x4A10_0818w : 32 word`;
val CPDMA_SOFT_RESET_PA_def = Define `CPDMA_SOFT_RESET_PA = 0x4A10_081Cw : 32 word`;
val DMACONTROL_PA_def = Define `DMACONTROL_PA = 0x4A10_0820w : 32 word`;
val RX_BUFFER_OFFSET_PA_def = Define `RX_BUFFER_OFFSET_PA = 0x4A10_0828w : 32 word`;
val TX0_HDP_PA_def = Define `TX0_HDP_PA = 0x4A10_0A00w : 32 word`;
val RX0_HDP_PA_def = Define `RX0_HDP_PA = 0x4A10_0A20w : 32 word`;
val TX0_CP_PA_def = Define `TX0_CP_PA = 0x4A10_0A40w : 32 word`;
val RX0_CP_PA_def = Define `RX0_CP_PA = 0x4A10_0A60w : 32 word`;
val CPPI_RAM_BYTE_PA_def = Define `CPPI_RAM_BYTE_PA pa = CPPI_RAM_START <=+ pa /\ pa <+ CPPI_RAM_END`;

val _ = export_theory();

