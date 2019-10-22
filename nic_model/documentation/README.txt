This project has formally verified in HOL4 that the NIC on BeagleBone Black
(SoC AM335x from Texas Instruments) can only read and write certain readable
and writable memory regions.

The structure of the directory formalization is as follows:
-/helper_tactics: Some commonly used tactics in the proofs.
-/model: The definition of the NIC.
-/bd_lemmas: Definitions and lemmas about writes to CPPI_RAM, buffer
 descriptors, and buffer descriptor queues.
-/automata_auxiliary_definitions_lemmas:
	-/bd_queues: Definitions and lemmas about the transmission and reception
	 buffer descriptor queues.
	-/lib: Definitions of SML functions used for automating proofs of lemmas.
	-/state_definitions: Definitions of predicates on the NIC state used for
	 readability regarding which state an automaton is in.
	-/state_lemmas: Lemmas involving the state definitions used for
	 readability.
	-/transition_definitions: Definitions of relations involving transitions
	 of automata and the NIC.
	-/transition_lemmas: Lemmas about automata and nic transitions.
-/invariant: Definition of the invariant. nic contains the definition of the
 NIC invariant.
-/invariant_preservation_lemmas:
	-/automata: Lemmas involving both automata and invariants. Most lemmas
	 relate the transitions of an automaton to the corresponding invariant,
	 with purpose of preserving that invariant.
	-/invariant: Lemmas used for preservation of invariants, not involving
	 automata transitions.
-/invariant_nic_transitions_preservation_proofs: Lemmas stating that each
 invariant is preserved by each automaton.
-/theorems: The five theorems stating that NIC register reads, autonomous and
 memory read reply transitions preserve the NIC invariant; and that memory read
 and write requests address only readable and writable memory, respectively.
