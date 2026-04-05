import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_le {s : Set R} {t : Subsemiring R} : Subsemiring.closure s ≤ t ↔ s ⊆ t := ⟨Set.Subset.trans Subsemiring.subset_closure, fun h => sInf_le h⟩

