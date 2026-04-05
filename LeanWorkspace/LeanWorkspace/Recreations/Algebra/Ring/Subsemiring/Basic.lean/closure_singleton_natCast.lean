import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_singleton_natCast (n : ℕ) : Subsemiring.closure {(n : R)} = ⊥ := bot_unique <| Subsemiring.closure_le.2 <| Set.singleton_subset_iff.mpr <| natCast_mem _ _

