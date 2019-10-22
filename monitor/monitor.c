#include <linux/io.h>		//For __iomem, __raw_readl and __raw_writel
#include <linux/kernel.h>	//For printk

//Size of NIC peripheral memory maps.
#define ss_small_size			0x0100	//Size of CPSW_SS up to CPSW_PORT.
#define ss_medium_size			0x1000	//Size of CPSW_SS up to MDIO.
#define ss_large_size			0x8000	//Size of CPSW_SS is 32KB.
#define port_size				0x0700
#define cpdma_size				0x0100
#define stats_size				0x0100
#define stateram_size			0x0200
#define cpts_size				0x0100
#define ale_size				0x0080
#define sl1_size				0x0040
#define sl2_size				0x0040
#define mdio_size				0x0100
#define wr_size					0x0D00
#define cppi_ram_size			0x2000

//Physical base addresses of NIC peripheral memory map.
#define ss_base_pa				0x4A100000
#define port_base_pa			0x4A100100
#define cpdma_base_pa			0x4A100800
#define stats_base_pa			0x4A100900
#define stateram_base_pa		0x4A100A00
#define cpts_base_pa			0x4A100C00
#define ale_base_pa				0x4A100D00
#define sl1_base_pa				0x4A100D80
#define sl2_base_pa				0x4A100DC0
#define mdio_base_pa			0x4A101000
#define wr_base_pa				0x4A101200
#define cppi_ram_base_pa		0x4A102000

//Returns true if and only if the physical address pa is in the indicated
//physical memory region.
#define is_ss_small_pa(pa)		(ss_base_pa <= pa && pa < ss_base_pa + ss_small_size)
#define is_ss_medium_pa(pa)		(ss_base_pa <= pa && pa < ss_base_pa + ss_medium_size)
#define is_ss_large_pa(pa)		(ss_base_pa <= pa && pa < ss_base_pa + ss_large_size)
#define is_port_pa(pa)			(port_base_pa <= pa && pa < port_base_pa + port_size)
#define is_cpdma_pa(pa)			(cpdma_base_pa <= pa && pa < cpdma_base_pa + cpdma_size)
#define is_stats_pa(pa)			(stats_base_pa <= pa && pa < stats_base_pa + stats_size)
#define is_stateram_pa(pa)		(stateram_base_pa <= pa && pa < stateram_base_pa + stateram_size)
#define is_cpts_pa(pa)			(cpts_base_pa <= pa && pa < cpts_base_pa + cpts_size)
#define is_ale_pa(pa)			(ale_base_pa <= pa && pa < ale_base_pa + ale_size)
#define is_sl1_pa(pa)			(sl1_base_pa <= pa && pa < sl1_base_pa + sl1_size)
#define is_sl2_pa(pa)			(sl2_base_pa <= pa && pa < sl2_base_pa + sl2_size)
#define is_mdio_pa(pa)			(mdio_base_pa <= pa && pa < mdio_base_pa + mdio_size)
#define is_wr_pa(pa)			(wr_base_pa <= pa && pa < wr_base_pa + wr_size)
#define is_cppi_ram_pa(pa)		(cppi_ram_base_pa <= pa && pa < cppi_ram_base_pa + cppi_ram_size)

//Given a physical address, computes the offset of that physical address relative
//the base physical address of the indicated memory region.
#define ss_offset_pa(pa)		(pa - ss_base_pa)
#define port_offset_pa(pa)		(pa - port_base_pa)
#define cpdma_offset_pa(pa)		(pa - cpdma_base_pa)
#define stats_offset_pa(pa)		(pa - stats_base_pa)
#define stateram_offset_pa(pa)	(pa - stateram_base_pa)
#define cpts_offset_pa(pa)		(pa - cpts_base_pa)
#define ale_offset_pa(pa)		(pa - ale_base_pa)
#define sl1_offset_pa(pa)		(pa - sl1_base_pa)
#define sl2_offset_pa(pa)		(pa - sl2_base_pa)
#define mdio_offset_pa(pa)		(pa - mdio_base_pa)
#define wr_offset_pa(pa)		(pa - wr_base_pa)
#define cppi_ram_offset_pa(pa)	(pa - cppi_ram_base_pa)

//Computes the virtual address of the given physical address if the physical
//address is in the indicated memory region.
#define ss_pa_to_va(pa)			(ss_base_va + ss_offset_pa(pa))
#define port_pa_to_va(pa)		(port_base_va + port_offset_pa(pa))
#define cpdma_pa_to_va(pa)		(cpdma_base_va + cpdma_offset_pa(pa))
#define stats_pa_to_va(pa)		(stats_base_va + stats_offset_pa(pa))
#define stateram_pa_to_va(pa)	(stateram_base_va + stateram_offset_pa(pa))
#define cpts_pa_to_va(pa)		(cpts_base_va + cpts_offset_pa(pa))
#define ale_pa_to_va(pa)		(ale_base_va + ale_offset_pa(pa))
#define sl1_pa_to_va(pa)		(sl1_base_va + sl1_offset_pa(pa))
#define sl2_pa_to_va(pa)		(sl2_base_va + sl2_offset_pa(pa))
#define mdio_pa_to_va(pa)		(mdio_base_va + mdio_offset_pa(pa))
#define wr_pa_to_va(pa)			(wr_base_va + wr_offset_pa(pa))
#define cppi_ram_pa_to_va(pa)	(cppi_ram_base_va + cppi_ram_offset_pa(pa))






//Offset relative ss_base_pa.
#define ss_offset_ss			(ss_base_pa			- ss_base_pa)
#define port_offset_ss			(port_base_pa		- ss_base_pa)
#define cpdma_offset_ss			(cpdma_base_pa		- ss_base_pa)
#define stats_offset_ss			(stats_base_pa		- ss_base_pa)
#define stateram_offset_ss		(stateram_base_pa	- ss_base_pa)
#define cpts_offset_ss			(cpts_base_pa		- ss_base_pa)
#define ale_offset_ss			(ale_base_pa		- ss_base_pa)
#define sl1_offset_ss			(sl1_base_pa		- ss_base_pa)
#define sl2_offset_ss			(sl2_base_pa		- ss_base_pa)

static uint32_t ss_base_va = 0;
static uint32_t mdio_base_va = 0;
static uint32_t wr_base_va = 0;
static uint32_t cppi_ram_base_va = 0;

//Virtual base addresses of the NIC peripherial memory map. The base addresses
//of CPSW_SS, CPSW_PORT, CPSW_CPDMA, CPSW_STATS, CPSW_STATE_RAM, CPSW_CTPS,
//CPSW_ALE, CPSW_SL1 and CPSW_SL2 are calculated with respect to CPSW_SS since
//cpsw.c:cpsw_probe() maps only CPSW_SS and CPSW_PORT, but accesses CPSW_CPDMA,
//CPSW_STATS, CPSW_STATE_RAM, CPSW_CTPS, CPSW_ALE, CPSW_SL1 and CPSW_SL2 as
//well. Since CPSW_PORT, CPSW_CPDMA, CPSW_STATS, CPSW_STATE_RAM, CPSW_CTPS,
//CPSW_ALE, CPSW_SL1 and CPSW_SL2 are located in the same 4kB page block as
//CPSW_SS, CPSW_PORT, CPSW_CPDMA, CPSW_STATS, CPSW_STATE_RAM, CPSW_CTPS,
//CPSW_ALE, CPSW_SL1 and CPSW_SL2 can be accessed through the same mapping.
#define ss_base_va				ss_base_va
#define port_base_va			(ss_base_va + port_offset_ss)
#define cpdma_base_va			(ss_base_va + cpdma_offset_ss)
#define stats_base_va			(ss_base_va + stats_offset_ss)
#define stateram_base_va		(ss_base_va + stateram_offset_ss)
#define cpts_base_va			(ss_base_va + cpts_offset_ss)
#define ale_base_va				(ss_base_va + ale_offset_ss)
#define sl1_base_va				(ss_base_va + sl1_offset_ss)
#define sl2_base_va				(ss_base_va + sl2_offset_ss)
#define mdio_base_va			mdio_base_va
#define wr_base_va				wr_base_va
#define cppi_ram_base_va		cppi_ram_base_va

//Returns true if and only if the virtual address va is mapped to the indicated
//physical memory region. It is assumed that virtual memory is mapped in
//continous 4kB blocks (cpsw.c maps CPSW_SS and CPSW_PORT but accesses
//additional unmapped addresses, but it works since those additional addresses
//are within the same 4kB block).
#define is_ss_small_va(va)		(ss_base_va <= va && va < ss_base_va + ss_small_size)
#define is_ss_medium_va(va)		(ss_base_va <= va && va < ss_base_va + ss_medium_size)
#define is_ss_large_va(va)		(ss_base_va <= va && va < ss_base_va + ss_large_size)
#define is_port_va(va)			(port_base_va <= va && va < port_base_va + port_size)
#define is_cpdma_va(va)			(cpdma_base_va <= va && va < cpdma_base_va + cpdma_size)
#define is_stats_va(va)			(stats_base_va <= va && va < stats_base_va + stats_size)
#define is_stateram_va(va)		(stateram_base_va <= va && va < stateram_base_va + stateram_size)
#define is_cpts_va(va)			(cpts_base_va <= va && va < cpts_base_va + cpts_size)
#define is_ale_va(va)			(ale_base_va <= va && va < ale_base_va + ale_size)
#define is_sl1_va(va)			(sl1_base_va <= va && va < sl1_base_va + sl1_size)
#define is_sl2_va(va)			(sl2_base_va <= va && va < sl2_base_va + sl2_size)
#define is_mdio_va(va)			(mdio_base_va <= va && va < mdio_base_va + mdio_size)
#define is_wr_va(va)			(wr_base_va <= va && va < wr_base_va + wr_size)
#define is_cppi_ram_va(va)		(cppi_ram_base_va <= va && va < cppi_ram_base_va + cppi_ram_size)

//Given a virtual address, computes the offset of that virtual address relative
//the base virtual address of the indicated memory map.
#define ss_offset_va(va)		(va - ss_base_va)
#define port_offset_va(va)		(va - port_base_va)
#define cpdma_offset_va(va)		(va - cpdma_base_va)
#define stats_offset_va(va)		(va - stats_base_va)
#define stateram_offset_va(va)	(va - stateram_base_va)
#define cpts_offset_va(va)		(va - cpts_base_va)
#define ale_offset_va(va)		(va - ale_base_va)
#define sl1_offset_va(va)		(va - sl1_base_va)
#define sl2_offset_va(va)		(va - sl2_base_va)
#define mdio_offset_va(va)		(va - mdio_base_va)
#define wr_offset_va(va)		(va - wr_base_va)
#define cppi_ram_offset_va(va)	(va - cppi_ram_base_va)

//Computes the physical address of the given virtual address if the virtual
//address is mapped to the indicated memory region.
#define ss_va_to_pa(va)			(ss_base_pa + ss_offset_va(va))
#define port_va_to_pa(va)		(port_base_pa + port_offset_va(va))
#define cpdma_va_to_pa(va)		(cpdma_base_pa + cpdma_offset_va(va))
#define stats_va_to_pa(va)		(stats_base_pa + stats_offset_va(va))
#define stateram_va_to_pa(va)	(stateram_base_pa + stateram_offset_va(va))
#define cpts_va_to_pa(va)		(cpts_base_pa + cpts_offset_va(va))
#define ale_va_to_pa(va)		(ale_base_pa + ale_offset_va(va))
#define sl1_va_to_pa(va)		(sl1_base_pa + sl1_offset_va(va))
#define sl2_va_to_pa(va)		(sl2_base_pa + sl2_offset_va(va))
#define mdio_va_to_pa(va)		(mdio_base_pa + mdio_offset_va(va))
#define wr_va_to_pa(va)			(wr_base_pa + wr_offset_va(va))
#define cppi_ram_va_to_pa(va)	(cppi_ram_base_pa + cppi_ram_offset_va(va))

void monitor_set_ss_base_va(void __iomem *va) {
	ss_base_va = (uint32_t) va;
	printk(KERN_INFO "monitor_set_mdio_ss_va: ss_base_va := 0x%p\n", va);
}

void monitor_set_wr_base_va(void __iomem *va) {
	wr_base_va = (uint32_t) va;
	printk(KERN_INFO "monitor_set_wr_base_va: wr_base_va := 0x%p\n", va);
}

void monitor_set_cppi_ram_base_va(void __iomem *va) {
	cppi_ram_base_va = (uint32_t) va;
	printk(KERN_INFO "monitor_set_cppi_ram_base_va: cppi_ram_base_va := 0x%p\n", va);
}

void monitor_set_mdio_base_va(void __iomem *va) {
	mdio_base_va = (uint32_t) va;
	printk(KERN_INFO "monitor_set_mdio_base_va: mdio_base_va := 0x%p\n", va);
}

static uint32_t va_to_pa(uint32_t va) {
	if (is_ss_small_va(va))
		return ss_va_to_pa(va);
	else if (is_port_va(va))
		return port_va_to_pa(va);
	else if (is_cpdma_va(va))
		return cpdma_va_to_pa(va);
	else if (is_stats_va(va))
		return stats_va_to_pa(va);
	else if (is_stateram_va(va))
		return stateram_va_to_pa(va);
	else if (is_cpts_va(va))
		return cpts_va_to_pa(va);
	else if (is_ale_va(va))
		return ale_va_to_pa(va);
	else if (is_sl1_va(va))
		return sl1_va_to_pa(va);
	else if (is_sl2_va(va))
		return sl2_va_to_pa(va);
	else if (is_mdio_va(va))
		return mdio_va_to_pa(va);
	else if (is_wr_va(va))
		return wr_va_to_pa(va);
	else if (is_cppi_ram_va(va))
		return cppi_ram_va_to_pa(va);
	else
		return 0;	//Virtual address unmapped. An error.
}

static uint32_t pa_to_va(uint32_t pa) {
	if (is_ss_small_pa(pa))
		return ss_pa_to_va(pa);
	else if (is_port_pa(pa))
		return port_pa_to_va(pa);
	else if (is_cpdma_pa(pa))
		return cpdma_pa_to_va(pa);
	else if (is_stats_pa(pa))
		return stats_pa_to_va(pa);
	else if (is_stateram_pa(pa))
		return stateram_pa_to_va(pa);
	else if (is_cpts_pa(pa))
		return cpts_pa_to_va(pa);
	else if (is_ale_pa(pa))
		return ale_pa_to_va(pa);
	else if (is_sl1_pa(pa))
		return sl1_pa_to_va(pa);
	else if (is_sl2_pa(pa))
		return sl2_pa_to_va(pa);
	else if (is_mdio_pa(pa))
		return mdio_pa_to_va(pa);
	else if (is_wr_pa(pa))
		return wr_pa_to_va(pa);
	else if (is_cppi_ram_pa(pa))
		return cppi_ram_pa_to_va(pa);
	else
		return 0;	//Physical address unmapped. An error.
}

static bool check_nic_register_write(uint32_t value, uint32_t pa);

void monitor__raw_writel(uint32_t value, volatile void *va) {
	uint32_t pa = va_to_pa((uint32_t) va);

	if (check_nic_register_write(value, pa))
		__raw_writel(value, va);
	else {
		printk(KERN_INFO "monitor__raw_writel: Illegal NIC register write: pa = %X, value = %X\n", pa, value);
		while(true);
	}
}

void monitor_writel(uint32_t value, volatile void *va) {
	uint32_t pa = va_to_pa((uint32_t) va);

	if (check_nic_register_write(value, pa))
		writel(value, va);
	else {
		printk(KERN_INFO "monitor_writel: Illegal NIC register write: pa = %X, value = %X\n", pa, value);
		while(true);
	}
}










/*
 * The following code consitutes the monitor.
 */

//Maximum length of a new buffer descriptor queue to add for transmission or
//reception. 256 buffer descriptors * 4 words per buffer descriptor * 4 bytes
//per word = 4KB. That is the half of CPPI_RAM. One half for transmission and
//one half for reception.
#define MAX_QUEUE_LENGTH 256

//Bit 31 is the SOP bit in a buffer descriptor.
#define SOP (1 << 31)
//Bit 30 is the EOP bit in a buffer descriptor.
#define EOP (1 << 30)
//Bit 29 is the OWNER bit in a buffer descriptor.
#define OWNER (1 << 29)
//Bit 28 is the EOQ bit in a buffer descriptor.
#define EOQ (1 << 28)
//Bit 27 is the Teardown bit in a buffer descriptor.
#define TD (1 << 27)
//Bit 26 is the CRC bit in a buffer descriptor.
#define CRC (1 << 26)

//Bits [10:0] is the Buffer Length field for reception buffer descriptors.
#define RX_BL 0x7FF
//Bits [26:16] is the Buffer Offset field for receive buffer descriptors.
#define RX_BO (0x7FF << 16)

//Bits [15:0] is the Buffer Length field for transmission buffer descriptors.
#define TX_BL 0xFFFF
//Bits [31:16] is the Buffer Offset field for transmission buffer descriptors.
#define TX_BO (0xFFFF << 16)

//Bits [10:0] is the Packet Length field for buffer descriptors.
#define PL 0x7FF

//The Next Descriptor Pointer has an offset 0 from the start of a buffer descriptor.
#define NEXT_DESCRIPTOR_POINTER 0
//The Buffer Pointer has an offset 4 from the start of a buffer descriptor.
#define BUFFER_POINTER 4
//The Buffer Offset and Buffer Length word has an offset 8 from the start of a buffer descriptor.
#define BOBL 8
//The word with flags has an offset 12 from the start of a buffer descriptor.
#define FLAGS 12

//Macro that checks word alignment.
#define is_word_aligned(address) ((address & 0x3) == 0)

//Teardown acknowledgement value.
#define TD_INT 0xFFFFFFFC

//Macros for classifying the type of queue.
#define TRANSMIT true
#define RECEIVE false

//Macros used for adding/removing a buffer descriptor to/from an active queue and marking the update in alpha.
#define ADD true
#define REMOVE false

//Macros used when manipulating SOP or EOP buffer descriptors.
#define SOP_BD true
#define EOP_BD false

//Macros for NIC register addresses.
#define TX_TEARDOWN_PA						0x4A100808
#define is_tx_teardown_pa(pa)				(pa == TX_TEARDOWN_PA)

#define RX_TEARDOWN_PA						0x4A100818
#define is_rx_teardown_pa(pa)				(pa == RX_TEARDOWN_PA)

#define CPDMA_SOFT_RESET_PA					0x4A10081C
#define is_cpdma_soft_reset_pa(pa)			(pa == CPDMA_SOFT_RESET_PA)

#define DMACONTROL_PA						0x4A100820
#define is_dmacontrol_pa(pa)				(pa == DMACONTROL_PA)

#define RX_BUFFER_OFFSET_PA					0x4A100828
#define is_rx_buffer_offset_pa(pa)			(pa == RX_BUFFER_OFFSET_PA)

#define is_hdp_register_pa(pa)				(0x4A100A00 <= pa && pa < 0x4A100A40)

#define TX0_HDP_PA							0x4A100A00
#define is_tx0_hdp_pa(pa)					(pa == TX0_HDP_PA)

#define RX0_HDP_PA							0x4A100A20
#define is_rx0_hdp_pa(pa)					(pa == RX0_HDP_PA)

#define is_cp_register_pa(pa)				(0x4A100A40 <= pa && pa < 0x4A100A80)

#define TX0_CP_PA							0x4A100A40
#define is_tx0_cp_pa(pa)					(pa == TX0_CP_PA)

#define RX0_CP_PA							0x4A100A60
#define is_rx0_cp_pa(pa)					(pa == RX0_CP_PA)

#define CPPI_RAM_START_PA					0x4A102000

//Enums used to denote what sort of overlap a CPPI_RAM does with respect to a queue.
typedef enum OVERLAP {NULL_NDP_OVERLAP, ILLEGAL_OVERLAP, NO_OVERLAP} bd_overlap;

//Physical addresses of buffer descriptors of the hypervisor's view of where
//the transmitter and receiver are in processing buffer descriptors. That is,
//the hypervisor's view of the active queues. They are updated on every
//CPPI_RAM access to give an accurate view of the current state of CPPI_RAM so
//that an access is not classified as accessing a buffer descriptor in use when
//the buffer descriptor in queustion has actually been released by the NIC
//hardware.
//
//tx0_active_queue and rx0_active_queue always point to a SOP.
static uint32_t tx0_active_queue = 0, rx0_active_queue = 0;
static bool initialized = false;
static bool tx0_hdp_initialized = false;
static bool rx0_hdp_initialized = false;
static bool tx0_cp_initialized = false;
static bool rx0_cp_initialized = false;
static bool tx0_tearingdown = false;
static bool rx0_tearingdown = false;

//For each 32-bit word aligned word in CPPI_RAM, true means that word is a part
//of an active queue, and false not.
#define alpha_SIZE 64
//This data structure assumes that no buffer descriptors overlap.
//By the definition of the C language is alpha initialized to contain only zeros.
static uint32_t alpha[alpha_SIZE];

//Input is a word aligned address in CPPI_RAM. The result is true if and only
//if that word is in use by the NIC, as seen by reading that word's bit in alpha.
/*
 1. WORD_INDEX := (CPPI_RAM_WORD - CPPI_RAM_START) >> 2
 2. uint32_t_index := WORD_INDEX / 32
 3. bit_offset := WORD_INDEX % 32
 4. (alpha[uint32_t_index] & (1 << bit_offset)) != 0

Optimized:
 1. uint32_t_index := ((CPPI_RAM_WORD - CPPI_RAM_START) >> 7)
 2. bit_offset := (((CPPI_RAM_WORD - CPPI_RAM_START) >> 2) & 0x1F)
 3. (alpha[(CPPI_RAM_WORD - CPPI_RAM_START) >> 7] & (1 << (((CPPI_RAM_WORD - CPPI_RAM_START) >> 2) & 0x1F)))
*/
#define IS_ACTIVE_CPPI_RAM(CPPI_RAM_WORD) (alpha[(CPPI_RAM_WORD - CPPI_RAM_START_PA) >> 7] & (1 << (((CPPI_RAM_WORD - CPPI_RAM_START_PA) >> 2) & 0x1F)))

//Input is a word aligned address in CPPI_RAM. The corresponding bit in alpha is set to 1.
#define SET_ACTIVE_CPPI_RAM(CPPI_RAM_WORD) (alpha[(CPPI_RAM_WORD - CPPI_RAM_START_PA) >> 7] |= (1 << (((CPPI_RAM_WORD - CPPI_RAM_START_PA) >> 2) & 0x1F)))

//Input is a word aligned address in CPPI_RAM. The corresponding bit in alpha is set to 0.
#define CLEAR_ACTIVE_CPPI_RAM(CPPI_RAM_WORD) (alpha[(CPPI_RAM_WORD - CPPI_RAM_START_PA) >> 7] &= (~(1 << (((CPPI_RAM_WORD - CPPI_RAM_START_PA) >> 2) & 0x1F))))

/*
 *  Local functions used only in this file.
 */
static bool stateram_handler(uint32_t);
static bool dmacontrol_handler(uint32_t);
static bool cpdma_soft_reset_handler(uint32_t);
static bool tx0_hdp_handler(uint32_t);
static bool rx0_hdp_handler(uint32_t);
static bool tx0_cp_handler(uint32_t);
static bool rx0_cp_handler(uint32_t);
static bool tx_teardown_handler(uint32_t);
static bool rx_teardown_handler(uint32_t);
static bool cppi_ram_handler(uint32_t, uint32_t);
static bool rx_buffer_offset_handler(uint32_t);

static void initialization_performed(void);
static void update_active_queue(bool);
static void update_alpha_queue(uint32_t, bool);
static void update_alpha(uint32_t, bool);
static bool is_queue_secure(uint32_t, bool);
static bool is_valid_length_in_cppi_ram_alignment_no_active_queue_overlap(uint32_t, bool);
static bool is_queue_self_overlap(uint32_t bd_ptr);
static bool is_transmit_SOP_EOP_packet_length_fields_set_correctly(uint32_t);
static bool is_data_buffer_secure_queue(uint32_t, bool);
static bool is_data_buffer_secure(uint32_t, bool);
static bool is_secure_linux_memory(bool, uint32_t, uint32_t);
static bd_overlap type_of_cppi_ram_access_overlap(uint32_t, uint32_t);
static void set_and_clear_word(uint32_t, uint32_t, uint32_t, uint32_t);
static void set_and_clear_word_on_sop_or_eop(uint32_t, uint32_t, uint32_t, uint32_t, bool);

static void print_queue(uint32_t);
static void print_active_queue(void);

//Reads 32-bit word at physical address pa.
static uint32_t read_nic_register(uint32_t pa) {
	uint32_t va = pa_to_va(pa);
	//__raw_readl(const volatile void __iomem *addr);

/*	if (((uint32_t)((volatile void __iomem *) va)) != va) {
		printk(KERN_INFO "read_nic_register: Cast error!\n");
		while(true);
	}*/

	return __raw_readl((volatile void __iomem *) va);
}

//Writes 32-bit word value at physical address pa.
static void write_nic_register(uint32_t pa, uint32_t value) {
	uint32_t va = pa_to_va(pa);
	//__raw_writel(u32 val, volatile void __iomem *addr);

/*	if (((uint32_t)((volatile void __iomem *) va)) != va) {
		printk(KERN_INFO "read_nic_register: Cast error!\n");
		while(true);
	}*/

	__raw_writel(value, (volatile void __iomem *) va);
}



//Macros for retrieving the content of a certain word of a buffer descriptor with physical address pa.
#define get_next_descriptor_pointer(bd_pa)		(read_nic_register(bd_pa + NEXT_DESCRIPTOR_POINTER))
#define get_buffer_pointer(bd_pa)				(read_nic_register(bd_pa + BUFFER_POINTER))
#define get_buffer_offset_and_length(bd_pa)		(read_nic_register(bd_pa + BOBL))
#define get_flags(bd_pa)						(read_nic_register(bd_pa + FLAGS))
#define get_rx_buffer_length(bd_pa)				(read_nic_register(bd_pa + BOBL) & RX_BL)
#define get_tx_buffer_length(bd_pa)				(read_nic_register(bd_pa + BOBL) & TX_BL)
#define get_packet_length(bd_pa)				(read_nic_register(bd_pa + FLAGS) & PL)

//Macros returning truth values depending on flag values of the given physical buffer descriptor address.
#define is_sop(bd_pa)							((read_nic_register(bd_pa + FLAGS) & SOP) != 0)
#define is_eop(bd_pa)							((read_nic_register(bd_pa + FLAGS) & EOP) != 0)
#define is_released(bd_pa)						((read_nic_register(bd_pa + FLAGS) & OWNER) == 0)
#define is_eoq(bd_pa)							((read_nic_register(bd_pa + FLAGS) & EOQ) != 0)
#define is_td(bd_pa)							((read_nic_register(bd_pa + FLAGS) & TD) != 0)







/*
 *  @pa: Physical address of accessed word that belongs to the Ethernet
 *  Subsystem. That is, its physical address is in [0x4A100000, 0x4A104000).
 *
 *  Returns: True if and only if the requested operation is secure: The NIC
 *  can only read and write readable and writable memory regions.
 */
static bool check_nic_register_write(uint32_t value, uint32_t pa)
{
	//If the accessed address is not word aligned, then an error occurred.
	if (!is_word_aligned(pa)) {
		printk(KERN_INFO "CPSW MONITOR: ACCESSED ADDRESS IS NOT WORD ALIGNED!");
		return false;
	} else {
		//For optimization the most commonly accessed registers are tested first.
		if (is_cppi_ram_pa(pa))						//CPPI_RAM
			return cppi_ram_handler(pa, value);
		else if (is_tx0_cp_pa(pa))					//TX0_CP
			return tx0_cp_handler(value);
		else if (is_rx0_cp_pa(pa))					//RX0_CP
			return rx0_cp_handler(value);
		else if (is_tx0_hdp_pa(pa))					//TX0_HDP
			return tx0_hdp_handler(value);
		else if (is_rx0_hdp_pa(pa))					//RX0_HDP
			return rx0_hdp_handler(value);
		else if (is_cpdma_soft_reset_pa(pa))		//CPDMA_SOFT_RESET
			return cpdma_soft_reset_handler(value);
		else if (is_dmacontrol_pa(pa))				//DMACONTROL
			return dmacontrol_handler(value);
		else if (is_tx_teardown_pa(pa))				//TX_TEARDOWN
			return tx_teardown_handler(value);
		else if (is_rx_teardown_pa(pa))				//RX_TEARDOWN
			return rx_teardown_handler(value);
		else if (is_rx_buffer_offset_pa(pa))		//RX_BUFFER_OFFSET
			return rx_buffer_offset_handler(value);
		else if (is_hdp_register_pa(pa))			//Tests T/X[i]_HDP := 0, must be after the T/RX0_HDP test above.
			return stateram_handler(value);
		else if (is_cp_register_pa(pa))				//Tests T/X[i]_CP := 0, must be after the T/RX0_CP test above.
			return stateram_handler(value);
		else										//The rest of the registers.
			return true;
	}
}

/*
 *  Purpose: Letting the guest initialize the TX[i]_HDP, RX[i]_HDP, TX[i]_CP
 *  and RX[i]_CP registers that are not used: 0 < i < 8.
 */
static bool stateram_handler(uint32_t val)
{
	if (val != 0 || !initialized)
		return false;
	else
		return true;
}

/*
 *  @val: The value to write the DMACONTROL register.
 *
 *  Function: Checks that the write to DMACONTROL is secure.
 *
 *  THE RX_OWNERSHIP BIT MUST NOT BE CHANGED SINCE CORRECT UPDATES OF
 *  rx0_active_queue DEPENDS ON IT.
 *
 *  @return: True if and only if the write was performed.
 */
static bool dmacontrol_handler(uint32_t val)
{
	if (val != 0 || !initialized)
		return false;
	else
		return true;
}

/*
 *  @val: The value to set the reset bit to.
 *
 *  Function: Sets the set reset bit in the CPDMA_SOFT_RESET register.
 *
 *  Returns: True if and only if the writing the reset bit succeeded.
 */
static bool cpdma_soft_reset_handler(uint32_t val)
{
	if (val == 0)
		return true;
	else if ((val & 0xFFFFFFFE) != 0 || !initialized || tx0_tearingdown || rx0_tearingdown)
		return false;
	else {
		initialized = false;
		tx0_hdp_initialized = false;
		rx0_hdp_initialized = false;
		tx0_cp_initialized = false;
		rx0_cp_initialized = false;
		return true;
	}
}

/*
 *  @bd_ptr: Physical address of the buffer descriptor that shall be written to
 *  TX0_HDP.
 *
 *  Function: Sets TX0_HDP to @bd_ptr if deemed appropriate.
 *
 *  Returns: True if and only if TX0_HDP is securely set to @bd_ptr.
 */
static bool tx0_hdp_handler(uint32_t bd_ptr)
{
	if (!initialized) {	//Performing initialization.
		if (read_nic_register(CPDMA_SOFT_RESET_PA) == 1 || bd_ptr != 0)
			return false;
		else {
			tx0_hdp_initialized = true;

			if (rx0_hdp_initialized && tx0_cp_initialized && rx0_cp_initialized)
				initialization_performed();

			return true;
		}
	} else {		//Initialization is done.
		if (read_nic_register(TX0_HDP_PA) != 0 || tx0_tearingdown)
			return false;
		else {
//			if (tx0_active_queue)
//				printk(KERN_INFO "tx0_hdp_handler: TX0_HDP = %X, tx0_active_queue = %X\n",
//					read_nic_register(TX0_HDP_PA), tx0_active_queue);

			//In this case, the initialization, and transmit teardown NIC processes are idle.
			//Hence tx0_active_queue, and ACTIVE_CPPI_RAM are updated to zero for the
			//buffer descriptors in tx0_active_queue.
//			update_active_queue(TRANSMIT);
			//The above is too slow since the NIC clears TX0_HDP before it has
			//cleared the ownership bits of all buffer descriptors in the queue.
			//Therefore, the NIC might add some buffer descriptors that are
			//considered to be in use, preventing the NIC driver from activating
			//transmission. The alpha data structure is therefore cleared.
			//tx0_active_queue is cleared to keep it synchronized with alpha.
			if (tx0_active_queue != 0) {
				update_alpha_queue(tx0_active_queue, REMOVE);
				tx0_active_queue = 0;
//				printk(KERN_INFO "tx0_hdp_handler: Updates alpha and tx0_active_queue.\n");
			}

			if (is_queue_secure(bd_ptr, TRANSMIT)) {
				tx0_active_queue = bd_ptr;
				update_alpha_queue(bd_ptr, ADD);
				return true;
			} else
				return false;
		}
	}
}

/*
 *  @bd_ptr: Physical address of the buffer descriptor that shall be written to
 *  RX0_HDP.
 *
 *  Function: Sets RX0_HDP to @bd_ptr if deemed appropriate.
 *
 *  Returns: True if and only if RX0_HDP is securely set to @bd_ptr.
 */
static bool rx0_hdp_handler(uint32_t bd_ptr)
{
	if (!initialized) {	//Performing initialization.
		if (read_nic_register(CPDMA_SOFT_RESET_PA) == 1 || bd_ptr != 0)
			return false;
		else {
			rx0_hdp_initialized = true;

			if (tx0_hdp_initialized && tx0_cp_initialized && rx0_cp_initialized)
				initialization_performed();

			return true;
		}
	} else {
		if (read_nic_register(RX0_HDP_PA) != 0 || rx0_tearingdown)
			return false;
		else {
			//In this case, the initialization, and transmit teardown NIC processes are idle.
			//Hence rx0_active_queue, and alpha are updated to zero for the
			//buffer descriptors in rx0_active_queue.
			update_active_queue(RECEIVE);
			if (is_queue_secure(bd_ptr, RECEIVE)) {
				rx0_active_queue = bd_ptr;
				update_alpha_queue(bd_ptr, ADD);
				return true;
			} else
				return false;
		}
	}
}

/*
 *  Purpose: Prevent the NIC to be set into an undefined state. That is to
 *  prevent making the NIC go into a state that is not specified by the
 *  specification.
 *
 *  @val: The value to seto TX0_CP to.
 *
 *  Function: Sets TX0_CP to @value if deemed appropriate.
 *
 *  Returns: True if and only if TX0_CP is securely set to @value.
 */
static bool tx0_cp_handler(uint32_t val)
{
	if (!initialized) {
		if (read_nic_register(CPDMA_SOFT_RESET_PA) == 1 || val != 0)
			return false;
		else {
			tx0_cp_initialized = true;

			if (tx0_hdp_initialized && rx0_hdp_initialized && rx0_cp_initialized)
				initialization_performed();

			return true;
		}
	} else {
		if (!tx0_tearingdown)
			return true;

		update_active_queue(TRANSMIT);	//If tx0_active_queue is 0, then teardown is complete.
		if (tx0_tearingdown && tx0_active_queue == 0 &&
				read_nic_register(TX0_CP_PA) == TD_INT &&
				read_nic_register(TX0_HDP_PA) == 0 && val == TD_INT) {
			tx0_tearingdown = false;
			return true;
		} else
			return false;
	}
}

/*
 *  Purpose: Prevent the NIC to be set into an undefined state. That is to
 *  prevent making the NIC go into a state that is not specified by the
 *  specification.
 *
 *  @val: The value to seto RX0_CP to.
 *
 *  Function: Sets RX0_CP to @value if deemed appropriate.
 *
 *  Returns: True if and only if RX0_CP is securely set to @value.
 */
static bool rx0_cp_handler(uint32_t val)
{
	if (!initialized) {
		if (read_nic_register(CPDMA_SOFT_RESET_PA) == 1 || val != 0)
			return false;
		else {
			rx0_cp_initialized = true;

			if (tx0_hdp_initialized && rx0_hdp_initialized && tx0_cp_initialized)
				initialization_performed();

			return true;
		}
	} else {
		if (!rx0_tearingdown)
			return true;

		update_active_queue(RECEIVE);
		if (rx0_tearingdown && rx0_active_queue == 0 &&
				read_nic_register(RX0_CP_PA) == TD_INT &&
				read_nic_register(RX0_HDP_PA) == 0 && val == TD_INT) {
			rx0_tearingdown = false;
			return true;
		} else
			return false;
	}
}

/*
 *  Purpose: Check valid behavior of the guest. Only channel zero is allowed to
 *  be used.
 *
 *  @channel: The DMA transmit channel to teardown.
 *
 *  Function: Initiate the teardown of DMA transmit channel zero.
 *
 *  Returns: True if and only if teardown was initiated for DMA transmit
 *  channel zero.
 */
static bool tx_teardown_handler(uint32_t channel)
{

	printk(KERN_INFO "tx_teardown_handler(%d)\n", channel);

	if (channel != 0 || !initialized || tx0_tearingdown)
		return false;
	else {
		tx0_tearingdown = true;
		return true;
	}
}

/*
 *  Purpose: Check valid behavior of the guest. Only channel zero is allowed to
 *  be used.
 *
 *  @channel: The DMA transmit channel to teardown.
 *
 *  Function: Initiate the teardown of DMA receive channel zero.
 *
 *  Returns: True if and only if teardown was initiated for DMA receive
 *  channel zero.
 */
static bool rx_teardown_handler(uint32_t channel)
{
	if (channel != 0 || !initialized || rx0_tearingdown)
		return false;
	else {
		rx0_tearingdown = true;
		return true;
	}
}

/*
 *  Purpose: Validity check of guest's access to CPPI_RAM. No non-guest memory
 *  is allowed to be accessed.
 *
 *  @pa: The physical address that is in the CPPI_RAM memory
 *  region that was tried to be written with the value @value.
 *
 *  @val: The value that the guest tried to write at physical address @pa.
 *
 *  Function: Making sure that the CPPI_RAM access cannot cause any disallowed
 *  memory accesses.
 *
 *  Returns: True if and only if the word @pa was set to @value.
 */
static bool cppi_ram_handler(uint32_t pa, uint32_t val)
{
	bd_overlap transmit_overlap;

	if (!initialized || tx0_tearingdown || rx0_tearingdown) {
		printk(KERN_INFO "INIT = %x | TX_TEARDOWN = %x | RX_TEARDOWN = %x\n", initialized, tx0_tearingdown, rx0_tearingdown);
		return false;
	}
	//Updates the tx0_active_queue and rx0_active_queue variables. This gives
	//a snapshot of which transmit and receive buffer descriptors are in use by
	//the NIC.
	update_active_queue(TRANSMIT);
	update_active_queue(RECEIVE);

	//pa is checked to be word aligned and in CPPI_RAM (since it
	//is also word aligned) in the top-level function. If it does not overlap
	//an active buffer descriptor, then the value can be written at that
	//location.
	if (!IS_ACTIVE_CPPI_RAM(pa))
		return true;

	//Checks what kind of overlap the CPPI_RAM access made.
	transmit_overlap = type_of_cppi_ram_access_overlap(pa, tx0_active_queue);

	//An access cannot overlap both the active transmit and receive queue since
	//they are word aligned, the access is word aligned, and the transmit and
	//receive queues do not overlap.
	//
	//If a zeroed next descriptor pointer overlap was identified, then it is
	//checked if the appended queue is secure. If it is not secure, then false
	//is returned and if it is secure, then @value is written at
	//@pa and true is returned.
	//
	//If there was an illegal overlap, then false is returned.
	//
	//Otherwise the receive case is checked in a similar manner.
	if (transmit_overlap == NULL_NDP_OVERLAP) {
		if (is_queue_secure(val, TRANSMIT)) {
			update_alpha_queue(val, ADD);
			return true;
		} else {
			printk(KERN_INFO "STH CPSW: APPENDED TRANSMISSION QUEUE IS INSECURE!\n");
			return false;
		}
	} else if (transmit_overlap == ILLEGAL_OVERLAP) {
		printk(KERN_INFO "STH CPSW: ILLEGAL TRANSMISSION OVERLAP!\n");
		return false;
	} else {
		bd_overlap receive_overlap = type_of_cppi_ram_access_overlap(pa, rx0_active_queue);
		if (receive_overlap == NULL_NDP_OVERLAP && is_queue_secure(val, RECEIVE)) {
			update_alpha_queue(val, ADD);
			return true;
		} else {
			printk(KERN_INFO "STH CPSW: ILLEGAL RECEPTION OVERLAP!\n");
			return false;
		}
	}
}

/*
 *  Purpose: Making sure that the RX_BUFFER_OFFSET register is not changed
 *  since the buffer length field of receive buffer descriptors must be greater
 *  than RX_BUFFER_OFFSET which might cause problems after data buffer memory
 *  accesses have been checked by is_data_buffer_secure().
 *
 *  @val: The value that the guest wants to set RX_BUFFER_OFFSET to.
 *
 *  Function: Checks that the guest does not try to changed the
 *  RX_BUFFER_OFFSET register to a value greater than zero.
 *
 *  Returns: True if and only if the NIC DMA hardware has been initialized and
 *  the value to write is zero.
 */
static bool rx_buffer_offset_handler(uint32_t val)
{
	//Only allow zero to be written for simplicity. Is used to guarantee that
	//nothing unspecified happens. The buffer offset field in receive buffer
	//descriptors must be greater than the value of this register. If this
	//RX_BUFFER_OFFSET register is changed after the data buffer memory
	//accesses check, it might affect the hardware operation if the buffer
	//length field is not greater than the RX_BUFFER_OFFSET register value.
	if (val != 0 || !initialized)
		return false;
	else
		return true;
}

/*
 *  Function: Update the array containing information about the NIC usage
 *  status of CPPI_RAM words and the tx0/rx0_active_queue variables.
 */
static void initialization_performed(void)
{
	int i;
	update_alpha_queue(tx0_active_queue, REMOVE);
	update_alpha_queue(rx0_active_queue, REMOVE);
	tx0_active_queue = 0;
	rx0_active_queue = 0;
	initialized = true;
	printk(KERN_INFO "monitor: initialization performed\n");
	for (i = 0; i < alpha_SIZE; i++)
		if (alpha[i] != 0) {
			printk(KERN_INFO "initialization_performed: alpha[%d] = %u\n", i, alpha[i]);
			while(true);
		}
}

/*
 *  Purpose: Update the snapshot view of where the NIC is with respect to
 *  transmission or reception.
 *
 *  Assumption: For transmission that the SOP and EOP bits are matching each
 *  other. For reception this is done by hardware.
 *
 *  @transmit: True if the tx0_active_queue shall be updated and false if the
 *  rx0_active_queue shall be updated.
 *
 *  Function: Update the hypervisor's view of which buffer descriptors are in
 *  use by the NIC, for transmission or reception depending on the value
 *  @transmit.
 *
 *  Returns: void.
 */
static void update_active_queue(bool transmit)
{
	uint32_t bd_ptr = transmit ? tx0_active_queue : rx0_active_queue;
	bool tearingdown = transmit ? tx0_tearingdown : rx0_tearingdown;
	bool released = true, no_teardown = true;

	//Exists a frame and its SOP buffer descriptor's Ownership bit has been
	//cleared.
	while (released && no_teardown && bd_ptr) {
		if (!is_released(bd_ptr))
			released = false;
		//Checks teardown bit. If it is set then the buffer descriptors are
		//released and alpha must be updated.
		else if (is_td(bd_ptr) && tearingdown) {
			update_alpha_queue(bd_ptr, REMOVE);
			no_teardown = false;
			bd_ptr = 0;
		} else {
			//Advances bd_ptr to point to the last buffer descriptor of the
			//current frame. That is one with EOP set.
			while (!is_eop(bd_ptr)) {
				update_alpha(bd_ptr, REMOVE);
				bd_ptr = get_next_descriptor_pointer(bd_ptr);
			}

			//Advances the buffer descriptor pointer to the next frame's SOP
			//buffer descriptor if there is one.
			update_alpha(bd_ptr, REMOVE);
			bd_ptr = get_next_descriptor_pointer(bd_ptr);
		}
	}

	//Updates the current head pointer to point to the first buffer
	//descriptor not released by the hardware for the queue.
	//printk(KERN_INFO "STH CPSW: update_active_queue, t/r(%d)x_active_queue = %x\n", transmit, bd_ptr);
	if (transmit)
		tx0_active_queue = bd_ptr;
	else
		rx0_active_queue = bd_ptr;

//	if (tx0_active_queue != 0 && read_nic_register(TX0_HDP_PA) == 0)
//		printk(KERN_INFO "update_active_queue: TX is done before clearing OWN!\n");
}

/*
 *  @bd_ptr: The physical address of the first buffer descriptor in a queue, in
 *  which all buffer descriptors are added or removed according to @add. For
 *	all buffer descriptors, rho_nic is decremented if @add is false, and alpha
 *	is updated depending on whether the buffer descriptors are added or removed.
 */
static void update_alpha_queue(uint32_t bd_ptr, bool add)
{
	while (bd_ptr) {
		update_alpha(bd_ptr, add);
		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}
}

/*
 *  @bd_ptr: The physical address of the buffer descriptor that is to be added
 *  or removed according to @add.
 *
 *	@transmit: True if the transmission queue is modified. False if it is the
 *	reception queue is modified.
 *
 *  @add: True if and only if the buffer descriptor at @bd_ptr is added to an
 *  active queue.
 *
 *  ASSUMES: bd_ptr is aligned and is in CPPI_RAM.
 *
 *  Function: If the buffer descriptor is added, alpha is updated. If the
 *	buffer descriptor is removed, rho_nic is decremented and alpha updated.
 *
 *  return: void.
 */
static void update_alpha(uint32_t bd_ptr, bool add)
{
	if (add) {
		SET_ACTIVE_CPPI_RAM(bd_ptr);
		SET_ACTIVE_CPPI_RAM(bd_ptr + 4);
		SET_ACTIVE_CPPI_RAM(bd_ptr + 8);
		SET_ACTIVE_CPPI_RAM(bd_ptr + 12);
//		printk(KERN_INFO "update_alpha() sets %X\n", bd_ptr);
	} else {
		CLEAR_ACTIVE_CPPI_RAM(bd_ptr);
		CLEAR_ACTIVE_CPPI_RAM(bd_ptr + 4);
		CLEAR_ACTIVE_CPPI_RAM(bd_ptr + 8);
		CLEAR_ACTIVE_CPPI_RAM(bd_ptr + 12);
//		printk(KERN_INFO "update_alpha() clears %X\n", bd_ptr);
	}
}

/*
 *  Purpose: Determine whether a queue to be set in an HDP register or appended
 *  to an active queue is secure.
 *
 *  @bd_ptr: Physical address of the first buffer descriptor in the queue to be
 *  checked for security.
 *
 *  @transmit: True if and only if the queue pointed by @head_bd_ptr is for
 *  transmission. Otherwise it is for reception.
 *
 *  Function: Returns true if and only if the queue @head_bd_ptr is secure. A
 *  queue is secure if and only if the following conditions are satisfied by
 *  the queue:
 *  a)  It has a length of at most MAX_QUEUE_LENGTH buffer descriptors.
 *  b)  All buffer descriptors are completely located in CPPI_RAM.
 *  c)  All buffer descriptors are word aligned.
 *  d)  None of its buffer descriptors overlap any buffer descriptor in any
 *		active queue (tx0_active_queue or rx0_active_queue).
 *  e)  None of its buffer descriptors overlap each other.
 *  f)  For transmission only: All buffer descriptors must have correctly
 *		matching SOP and EOP bits.
 *  g)  All buffer descriptors only access the memory of the guest and that the
 *		buffer length field is greater than zero. For the monitor and receive
 *		queues, no buffer descriptor is allowed to access executable memory.
 *	h)	REMOVED SINCE RHO_NIC IS NOT RELEVANT ANYMORE.
 *  i)  For transmission only: The following fields must be set accordingly:
 *		-Ownership: 1. Only valid on SOP.
 *		-EOQ: 0. Only valid on EOP.
 *		-Teardown: 0. Only valid on SOP.
 *  j)  For reception only: The following fields must be set accordingly:
 *		-Buffer offset: 0. Only valid on SOP but should be cleared on all
 *		 buffer descriptors.
 *		-SOP: 0. Valid on all buffer descriptors.
 *		-EOP: 0. Valid on all buffer descriptors.
 *		-Ownership: 1. Valid on all buffer descriptors.
 *		-EOQ: 0. Valid on all buffer descriptors.
 *		-Teardown: 0. For initialization, should be cleared in all buffer
 *		 descriptors.
 *		-CRC: 0. For initialization, should be cleared in all buffer
 *		 descriptors.
 *
 *  Returns: True if and only if the queue pointed to by @bd_ptr is secure.
 *  Such a queue can be given to the NIC hardware.
 */
static bool is_queue_secure(uint32_t bd_ptr, bool transmit)
{
	//An empty queue is secure.
	if (bd_ptr == 0)
		return true;

	//a), b), c), d).
	if (!is_valid_length_in_cppi_ram_alignment_no_active_queue_overlap(bd_ptr, transmit)) {
		printk(KERN_INFO "STH CPSW ERROR: Not valid length, in CPPI_RAM or alignment for queue at %x\n", bd_ptr);
		return false;
	}
	//e).
	if (is_queue_self_overlap(bd_ptr)) {
		printk(KERN_INFO "STH CPSW ERROR: Queue overlaps itself for queue beginning at %x\n", bd_ptr);
		return false;
	}
	//f).
	if (transmit && !is_transmit_SOP_EOP_packet_length_fields_set_correctly(bd_ptr)) {
		printk(KERN_INFO "STH CPSW ERROR: Queue is of transmit type and does not have correctly matching SOP and EOP bits for queue starting at %x\n", bd_ptr);
		return false;
	}
	//g).
	if (!is_data_buffer_secure_queue(bd_ptr, transmit)) {
		printk(KERN_INFO "STH CPSW ERROR: Queue accesses memory outside the guest or buffer length is zero for queue starting at %x\n", bd_ptr);
		return false;
	}

	//Now that it is known that the buffer descriptors are not overlapping,
	//nor used by the NIC, and the buffer descriptors are word aligned, they
	//can be recorded as given to the NIC (rho_nic and recv_bd_nr_blocks) and
	//manipulated to have correctly configured bits.

	//h). REMOVED SINCE RHO_NIC IS NOT RELEVANT ANYMORE.

	//i).
	if (transmit) {
		set_and_clear_word_on_sop_or_eop(bd_ptr, FLAGS, OWNER, 0, SOP_BD);		//Sets Owner bit on SOP.
		set_and_clear_word_on_sop_or_eop(bd_ptr, FLAGS, 0, EOQ, EOP_BD);		//Clears EOQ bit on EOP.
		set_and_clear_word_on_sop_or_eop(bd_ptr, FLAGS, 0, TD, SOP_BD);			//Clears TD bit on SOP.
	}
	//j).
	else {
		set_and_clear_word(bd_ptr, BOBL, 0, RX_BO);								//Clears buffer offset.
		set_and_clear_word(bd_ptr, FLAGS, OWNER, SOP | EOP | EOQ | TD | CRC);	//Sets owner, clears SOP, EOP, EOQ, TD, CRC.
	}

	//No security violations and therefore true is returned.
	return true;
}

/*
 *  Purpose: Modifies certain bits of certain words of SOP or EOP buffer
 *  descriptors only in a transmit queue. (Receive queues have both SOP and EOP
 *  bits cleared.)
 *
 *  @bd_ptr: Physical address of the head of the queue to be operated on.
 *
 *  @offset: Number of bytes of the word to be accessed from the start of the
 *  buffer descriptor. MUST BE WORD ALIGNED.
 *
 *  @set: A bit mask with ones at the positions that shall be set in the word
 *  with the byte offset indicated by @offset for every buffer descriptor in
 *  the queue that is of the type indicated by @sop. Should be disjunctive with
 *  @clear.
 *
 *  @clear: A bit mask with ones at the positions that shall be cleared in the
 *  word with the byte offset indicated by @offset for every buffer descriptor
 *  in the queue that is of the type indicated by @sop. Should be disjunctive
 *  with @set.
 *
 *  @modify_sop_or_eop: True if SOP buffer descriptors shall be manipulated,
 *	and false if EOP buffer descriptors shall be manipulated.
 *
 *  Termination: The queue pointed to by bd_ptr must be finite.
 *
 *  Function: For each buffer descriptor of type indicated by @sop in the queue
 *  pointed to by bd_ptr, the word with @offset bytes is set to:
 *  word := (word | set) & ~clear.
 *
 *  Returns: void.
 */
static void set_and_clear_word_on_sop_or_eop(uint32_t bd_ptr, uint32_t offset, uint32_t set, uint32_t clear, bool modify_sop_or_eop)
{
	while (bd_ptr) {
		//Remember that a buffer descriptor can be both of type SOP and EOP.
		if ((is_sop(bd_ptr) && modify_sop_or_eop) || (is_eop(bd_ptr) && !modify_sop_or_eop)) {
			uint32_t new_val = (read_nic_register(bd_ptr + offset) | set) & ~clear;
			write_nic_register(bd_ptr + offset, new_val);
		}
		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}
}

/*
 *  Purpose: Modifies certain bits of certain words of all buffer descriptors
 *  in a queue.
 *
 *  @bd_ptr: Physical address of the head of the queue to be operated on.
 *
 *  @offset: Number of bytes of the word to be accessed from the start of the
 *  buffer descriptor. MUST BE WORD ALIGNED.
 *
 *  @set: A bit mask with ones at the positions that shall be set in the word
 *  with the byte offset indicated by @offset for every buffer descriptor in
 *  the queue. Should be disjunctive with @clear.
 *
 *  @clear: A bit mask with ones at the positions that shall be cleared in the
 *  word with the byte offset indicated by @offset for every byffer descriptor
 *  in the queue. Should be disjunctive with @set.
 *
 *  Termination: The queue pointed to by bd_ptr must be finite.
 *
 *  Function: For each buffer descriptor in the queue pointed to by bd_ptr the
 *  fourth word is set to: word := (word | set) & ~clear
 */
static void set_and_clear_word(uint32_t bd_ptr, uint32_t offset, uint32_t set, uint32_t clear)
{
	while (bd_ptr) {
		uint32_t new_val = (read_nic_register(bd_ptr + offset) | set) & ~clear;
		write_nic_register(bd_ptr + offset, new_val);

		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}
}

/*
 *  Purpose: Checks that a queue is finite by restricting its length to be at
 *  most 256 buffer descriptors, that it is completely located in CPPI_RAM,
 *  that all buffer descriptors are word aligned, and that it does not overlap
 *	an active queue.
 *
 *  @bd_ptr: Physical address of the first buffer descriptor of the queue to
 *  check.
 *
 *  Function: Checks that the queue headed by @bd_ptr satisfies:
 *  a)  It has a length of at most MAX_QUEUE_LENGTH buffer descriptors.
 *  b)  All buffer descriptors are completely located in CPPI_RAM.
 *  c)  All buffer descriptors are word aligned.
 *  d)  No overlap with an active queue.
 *
 *  Returns: True if and only if the queue headed by @bd_ptr is of valid,
 *  length, located in CPPI_RAM, word aligned, and does not overlap an active
 *  queue.
 */
static bool is_valid_length_in_cppi_ram_alignment_no_active_queue_overlap(uint32_t bd_ptr, bool transmit)
{
	int length = 0;
	while (bd_ptr != 0 && length < MAX_QUEUE_LENGTH)
		//Subtracts fifteen bytes from 0x4A104000 instead from bd_ptr to avoid
		//overflow, which would create a false truth value. Also checks that
		//all buffer descriptor pointers are word aligned.
		if ((0x4A102000 <= bd_ptr) && (bd_ptr < (0x4A104000 - 15)) && is_word_aligned(bd_ptr)) {
			if (IS_ACTIVE_CPPI_RAM(bd_ptr) || IS_ACTIVE_CPPI_RAM(bd_ptr + 4) || IS_ACTIVE_CPPI_RAM(bd_ptr + 8) || IS_ACTIVE_CPPI_RAM(bd_ptr + 12)) {
				printk(KERN_INFO "STH CPSW: New buffer descriptor overlaps active buffer descriptor (tx = %d; TX0_HDP = %X, RX0_HDP = %X, rx0_active_queue = %X).\n", transmit, read_nic_register(TX0_HDP_PA), read_nic_register(RX0_HDP_PA), rx0_active_queue);

				print_queue(rx0_active_queue);
				print_active_queue();
				return false;
			}

			length += 1;
			bd_ptr = get_next_descriptor_pointer(bd_ptr);
		} else {
			printk(KERN_INFO "STH CPSW: Buffer descriptor not completely located in CPPI_RAM or is not word aligned.\n");
			return false;
		}

	//If the queue consists of more than MAX_QUEUE_LENGTH buffer descriptors,
	//the function returns false.
	if (bd_ptr) {
		printk(KERN_INFO "STH CPSW: New queue is longer than %d!\n", MAX_QUEUE_LENGTH);
		return false;
	}
	//No policy violations and true is returned.
	return true;
}

/*
 *  Purpose: Checks if a queue does not overlap itself.
 *
 *  Assumption: The input queue is in CPPI_RAM and word aligned. Hence no
 *  overflow and only multiples of four needs to be compared for the addresses.
 *
 *  @bd_ptr: Physical address of the queue to be checked.
 *
 *  Termination: Guaranteed.
 *
 *  Function: Checks that the queue headed by @bd_ptr satisfies:
 *  e)  None of its buffer descriptors overlap each other.
 *
 *  Returns: True if and only if the queue pointed to by @bd_ptr overlaps itself.
 */
static bool is_queue_self_overlap(uint32_t bd_ptr)
{
	//Check self overlap. No form of cyclic queue is allowed. Alignment of all
	//buffer descriptors is assumed which is also true due to the test above.
	while (bd_ptr) {
		//Compares bd_ptr with all buffer descriptors following it.
		uint32_t other_bd_ptr = get_next_descriptor_pointer(bd_ptr);
		while (other_bd_ptr)
			if ((bd_ptr <= other_bd_ptr && other_bd_ptr < bd_ptr + 0x10) || (other_bd_ptr <= bd_ptr && bd_ptr < other_bd_ptr + 0x10)) {
				printk(KERN_INFO "STH CPSW: Buffer descriptor queue overlaps itself!\n");
				return true;
			} else
				other_bd_ptr = get_next_descriptor_pointer(other_bd_ptr);

		//Advances bd_ptr to the next buffer descriptor that should be compared
		//with the buffer descriptors following it.
		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}

	//No self-overlap error was found.
	return false;
}

/*
 *  Purpose: Check that a transmit queue has its SOP and EOP bits set correctly
 *  such that updates of tx0_active_queue can be done correctly. Updates of
 *  tx0_active_queue depend on the Ownership bit which is only set in SOP
 *  buffer descriptors. To make tx0_active_queue point to the next unreleased
 *  buffer descriptor by the hardware, these bits must be set correctly.
 *
 *  Assumption: Input queue is for transmission in CPPI_RAM and the first
 *  buffer descriptor is a SOP.
 *    
 *  ATTENTION: THIS CHECK IS NECESSARY SINCE THE CALCULATION OF ACTIVE QUEUES
 *  DEPENDS ON CORRECT SETTING OF SOP AND EOP BITS.
 *
 *  @bd_ptr: Physical address of the first buffer descriptor in the transmit
 *  queue to check for correct setting of the SOP and EOP bits.
 *
 *  Function: Checks that the queue headed by @bd_ptr satisifies:
 *  f)  For transmission only: all buffer descriptors must have correctly
 *		matching SOP and EOP bits.
 *
 *  Returns: True if and only if all SOP and EOP bits matched correctly: Every
 *  SOP bit is followed by an EOP bit (could be in same buffer descriptor)
 *  before the next SOP bit and the queue always ends with an EOP bit.
 */
static bool is_transmit_SOP_EOP_packet_length_fields_set_correctly(uint32_t bd_ptr)
{
	uint32_t buffer_length_sum, packet_length;

	//Goes through each frame's buffer descriptors, that is the whole queue but
	//one SOP ... EOP sequence at a time.
	//While there is a frame...
	while (bd_ptr) {
		//If the first buffer descriptor is not a SOP, then there is an error.
		if (!is_sop(bd_ptr)) {
			printk(KERN_INFO "STH CPSW: Transmission queue is rejected due to invalid SOP/EOP sequence of buffer descriptors!\n");
			return false;
		}
		buffer_length_sum = get_tx_buffer_length(bd_ptr);
		packet_length = get_packet_length(bd_ptr);

		//If the first buffer descriptor is not an EOP, then such a buffer
		//descriptor must be found.
		if (!is_eop(bd_ptr)) {
			bd_ptr = get_next_descriptor_pointer(bd_ptr);
			//At this point the queue looks like: [BD.SOP], [BD.X] ... And bd_ptr
			//points to [BD.X].

			//Until a null pointer, SOP or EOP buffer descriptor is found, bd_ptr
			//is advanced.
			while (bd_ptr != 0 && !is_sop(bd_ptr) && !is_eop(bd_ptr)) {
				buffer_length_sum += get_tx_buffer_length(bd_ptr);
				bd_ptr = get_next_descriptor_pointer(bd_ptr);
			}
			if (bd_ptr)
				buffer_length_sum += get_tx_buffer_length(bd_ptr);

			//If it wasn't an EOP that stopped the processing, then it is an error.
			//Even if EOP was set, SOP must not be set for a valid matching.
			if (bd_ptr == 0 || is_sop(bd_ptr)) {
				printk(KERN_INFO "STH CPSW: Transmission queue is rejected due to invalid SOP/EOP sequence of buffer descriptors!\n");
				return false;
			}
		}
		//Checks that the sum of the buffer length fields are equal to the
		//packet length field.
		if (packet_length != buffer_length_sum) {
			printk(KERN_INFO "STH CPSW: Transmission queue is rejected due to invalid packet length field of a transmit SOP buffer descriptors!\n");
			return false;
		}
		//At this point, bd_ptr is an EOP buffer descriptor. Hence bd_ptr is
		//advanced to the next frame's first buffer descriptor.
		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}

	//No policy violation and therefore true is returned.
	return true;
}

/*
 *  Purpose: Checks that a queue is valid: All buffer descriptors refer to data
 *  buffers that are in the guest's memory region, that the buffer length field
 *  is greater than zero and if the monitor is used, that receive buffer
 *  descriptors cannot access executable memory.
 *
 *  Assumptions: Queue is in CPPI_RAM and word aligned.
 *
 *  @bd_ptr: The physical address of the first buffer descriptor in the queue.
 *
 *  @transmit: True if and only if the queue is for transmission.
 *
 *  Termination: If the queue is of finite length.
 *
 *  Function: Checks that the queue headed by bd_ptr satisifes:
 *  g)  All buffer descriptors only access the memory of the guest and their
 *		buffer length field is greater than zero. For the monitor it is checked
 *		that receive buffer descriptors cannot access executable memory.
 *
 *  Returns: True if and only if the queue pointed to by @bd_ptr only access
 *  memory of the guest, the buffer length field is greater than zero, and if
 *  the monitor is used no executable memory is accessed.
 */
static bool is_data_buffer_secure_queue(uint32_t bd_ptr, bool transmit)
{
	while (bd_ptr) {
		if (!is_data_buffer_secure(bd_ptr, transmit)) {
			printk(KERN_INFO "STH CPSW: Insecure buffer descriptor rejected!\n");
			return false;
		}

		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}

	//No error was found and hence true is returned.
	return true;
}

/*
 *  Purpose: Checks that a buffer descriptor only refers to memory of the
 *  guest, that the buffer length field is greater than zero, and if the
 *  monitor is used no executable memory is accessed by receive buffer
 *  descriptors.
 *
 *  Assumptions:
 *  *Assumes that if @bd_ptr is a receive queue, then the buffer offset field
 *   of all buffer descriptors have been cleared. This could be dangerous if
 *   the hardware ORed the bits in the buffer descriptor with the
 *   RX_BUFFER_OFFSET register.
 *  *If @bd_ptr is belongs to a transmit queue and is a SOP buffer descriptor,
 *   then its related buffer descriptors belonging to the same frame, can be
 *   found by following the next descriptor pointer fields until the EOP buffer
 *   descriptor.
 *
 *  @bd_ptr: The physical address of the buffer descriptor.
 *
 *  @transmit: True if and only if the queue is of transmission type.
 *
 *  Termination: Guaranteed.
 *
 *  Function: Checks that the buffer descriptor, of the type indicated by
 *  @transmit, pointed to by @bd_ptr represents a data buffer that is within
 *  the guest's physical memory region, that the buffer length is greater than
 *  zero, and if monitor is used, then no executable memory is accessed by
 *  receive buffer descriptors.
 *
 *  Returns: True if and only if the buffer descriptor pointed to by bd_ptr
 *  represents a data buffer that is within the guests physical memory region,
 *  that the buffer length field is greater than zero, and if monitor is used,
 *  then no executable memory is accessed by receive buffer descriptors.
 */
static bool is_data_buffer_secure(uint32_t bd_ptr, bool transmit)
{
	uint32_t buffer_pointer = get_buffer_pointer(bd_ptr), buffer_offset, buffer_length;
	uint32_t buffer_offset_length = get_buffer_offset_and_length(bd_ptr);
	uint32_t start_bl, end_bl;

	//Retrieves the buffer offset and buffer length fields, the sizes of which
	//depends on whether they are part of a transmit or receive buffer descriptor.
	if (transmit) {		//If a transmit buffer descriptor.
		if (is_sop(bd_ptr))	//If a SOP buffer descriptor then must the buffer offset field be checked.
			buffer_offset = (buffer_offset_length & TX_BO) >> 16;
		else
			//Buffer offset is only relevant for SOP buffer descriptors and is zero for other ones.
			buffer_offset = 0;

		buffer_length = buffer_offset_length & TX_BL;
	} else {		//If a receive buffer descriptor.
		buffer_offset = 0;	//Buffer offset is only relevant for SOP buffer descriptors and should always be initialized to zero by
		//software. Overwritten by the hardware with the value in the RX_BUFFER_OFFSET register in SOP buffer
		//descriptors. The buffer length field indicates the size of the buffer and the RX_BUFFER_OFFSET register
		//cannot make data be stored outside the data buffer associated with the buffer descriptor.
		buffer_length = buffer_offset_length & RX_BL;
	}

	//Checks that buffer length is greater than zero.
	if (buffer_length == 0) {
		printk(KERN_INFO "STH CPSW: Buffer length is zero for buffer descriptor at %x!\n", bd_ptr);
		return false;
	}
	//Checks overflow condition.
	//The buffer may not wrap.
	//There is an overflow if
	//buffer_pointer + buffer_offset + buffer_length - 1 > 0xFFFFFFFF <==>
	//buffer_pointer > 0xFFFFFFFF - buffer_offset - buffer_length + 1.
	//Now underflow since buffer_offset and buffer_length is at most 2^16 - 1
	//and their sum is at most 2^17 - 2.
	if (buffer_pointer > 0xFFFFFFFF - buffer_offset - buffer_length + 1) {
		printk(KERN_INFO "STH CPSW: Data buffer calculation overflow!\n");
		return false;
	}

	start_bl = buffer_pointer >> 12;
	end_bl = (buffer_pointer + buffer_offset + buffer_length - 1) >> 12;
	if (!is_secure_linux_memory(transmit, start_bl, end_bl)) {
		printk(KERN_INFO "STH CPSW: Buffer descriptor is not addressing legal memory.\n");
		return false;
	}
	//No errors, and hence the buffer descriptor is valid.
	return true;
}

/*
 *	@transmit: True if the security check is with respect to a transmission
 *	buffer descriptor and false if it is with respect to a reception buffer
 *	descriptor.
 *
 *	@start_bl: Block index of the first block that shall be checked.
 *
 *	@end_bl: Block index of the last block that shall be checked.
 *
 *	Returns: True if and only if the blocks with indexes between current_bl and
 *	end_bl, inclusive, only access Linux RAM, and for reception also no page
 *	tables, NIC registers or executable memory.
 */
static bool is_secure_linux_memory(bool transmit, uint32_t start_bl, uint32_t end_bl)
{
	//The blocks address only allowed RAM and therefore are there no security issues.
	return true;
}

/*
 *  Purpose: Determine what sort of access is made to a queue: zeroed next
 *  descriptor pointer, other accesses on the queue, and no access at all.
 *
 *  Assumptions: The queue identified by @bd_ptr and @pa are word
 *  aligned.
 *
 *  @accessed_address: Physical address of CPPI_RAM that is to be written.
 *
 *  @bd_ptr: The physical address of the first buffer descriptor in the
 *  queue to check overlap with.
 *
 *  Function: Returns a value of type bd_overlap which is an enum:
 *  *NULL_NDP_OVERLAP: @pa accesses a zeroed next descriptor pointer.
 *  *ILLEGAL_OVERLAP: @pa accesses a illegad buffer descriptor
 *   word.
 *  *NO_OVERLAP: @pa does not access any byte of any buffer
 *   descriptor.
 */
static bd_overlap type_of_cppi_ram_access_overlap(uint32_t accessed_address, uint32_t bd_ptr)
{
	while (bd_ptr)
		if (bd_ptr == accessed_address) {
			if (get_next_descriptor_pointer(bd_ptr) == 0)
				return NULL_NDP_OVERLAP;
			else
				return ILLEGAL_OVERLAP;
		} else if (bd_ptr < accessed_address && accessed_address <= bd_ptr + 0xF)
			return ILLEGAL_OVERLAP;
		else
			bd_ptr = get_next_descriptor_pointer(bd_ptr);

	return NO_OVERLAP;
}

static void print_queue(uint32_t bd_ptr)
{
	printk(KERN_INFO "-----DEBUGGING INFORMATION QUEUE-----\n");
	printk(KERN_INFO "TX0_HDP,tx0_active_queue = (%x, %x)\n", read_nic_register(TX0_HDP_PA), tx0_active_queue);
	printk(KERN_INFO "RX0_HDP,tx0_active_queue = (%x, %x)\n", read_nic_register(RX0_HDP_PA), rx0_active_queue);
	while (bd_ptr) {
		uint32_t ndp = get_next_descriptor_pointer(bd_ptr);
		uint32_t bp = get_buffer_pointer(bd_ptr);
		uint32_t bobl = get_buffer_offset_and_length(bd_ptr);
		uint32_t mode = get_flags(bd_ptr);
		printk(KERN_INFO "########################################\n");
		printk(KERN_INFO "Buffer Descriptor at: %x\n", bd_ptr);
		printk(KERN_INFO "Next Buffer Descriptor Pointer: %x\n", ndp);
		printk(KERN_INFO "Buffer Pointer: %x\n", bp);
		printk(KERN_INFO "Buffer Offset and Buffer Length: %x\n", bobl);
		printk(KERN_INFO "SOP = %d EOP = %d OWNER = %d EOQ = %d Teardown = %d\n",
		     (mode & SOP) >> 31, (mode & EOP) >> 30,
		     (mode & OWNER) >> 29, (mode & EOQ) >> 28,
		     (mode & TD) >> 27);
		printk(KERN_INFO "########################################\n");
		bd_ptr = get_next_descriptor_pointer(bd_ptr);
	}
	printk(KERN_INFO "-----------------------------------------------------\n");
}

static void print_active_queue(void) {
	unsigned int pa;
	printk(KERN_INFO "-----DEBUGGING INFORMATION CURRENT ACTIVE QUEUE-----\n");
	for (pa = CPPI_RAM_START_PA; is_cppi_ram_pa(pa); pa++)
		if (IS_ACTIVE_CPPI_RAM(pa))
			printk(KERN_INFO "Word at %X in CPPI_RAM is active.\n", pa);
	printk(KERN_INFO "-----------------------------------------------------\n");
}

//Performs a reset. The Linux NIC driver does not perform a reset before
//writing to CPPI_RAM, which is required by the monitor. Therefore, this
//function is invoked early by the the Linux NIC driver.
void monitor_perform_reset(void) {
	unsigned int i;
	printk(KERN_INFO "monitor_perform_reset()\n");

	if (read_nic_register(CPDMA_SOFT_RESET_PA) != 0 || tx0_tearingdown || rx0_tearingdown) {
		printk(KERN_INFO "perform_reset: Cannot reset since reset or teardown is active.\n");
		while(true);
	}


	write_nic_register(CPDMA_SOFT_RESET_PA, 1);

	while (read_nic_register(CPDMA_SOFT_RESET_PA));

	for (i = 0; i < 8; i++) {
		write_nic_register(0x4A100A00 +  0 * 4 + 4 * i, 0);
		write_nic_register(0x4A100A00 +  8 * 4 + 4 * i, 0);
		write_nic_register(0x4A100A00 + 16 * 4 + 4 * i, 0);
		write_nic_register(0x4A100A00 + 24 * 4 + 4 * i, 0);
	}

	write_nic_register(RX_BUFFER_OFFSET_PA, 0);

	initialized = true;
	tx0_hdp_initialized = true;
	rx0_hdp_initialized = true;
	tx0_cp_initialized = true;
	rx0_cp_initialized = true;

	for (i = 0; i < alpha_SIZE; i++)
		if (alpha[i] != 0) {
			printk(KERN_INFO "monitor_perform_reset: alpha[%d] = %u\n", i, alpha[i]);
			while(true);
		}
}
