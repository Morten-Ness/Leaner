import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : Subsemiring.closure s ≤ Subsemiring.closure t := Subsemiring.closure_le.2 <| Set.Subset.trans h Subsemiring.subset_closure

