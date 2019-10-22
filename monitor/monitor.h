//#include <linux/io.h>		//For __iomem, but includes __raw_readl and __raw_writel. Not needed since the Linux NIC driver already includes it.

//The following seven functions constitute the interface to the Linux NIC driver.
void monitor_set_ss_base_va(void __iomem *va);
void monitor_set_wr_base_va(void __iomem *va);
void monitor_set_cppi_ram_base_va(void __iomem *va);
void monitor_set_mdio_base_va(void __iomem *va);

void monitor__raw_writel(u32 value, volatile void *virtual_address);
void monitor_writel(u32 value, volatile void *virtual_address);

void monitor_perform_reset(void);
