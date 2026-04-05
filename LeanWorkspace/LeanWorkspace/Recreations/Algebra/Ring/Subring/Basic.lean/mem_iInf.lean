import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_iInf {ι : Sort*} {S : ι → Subring R} {x : R} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Subring.mem_sInf, Set.forall_mem_range]

