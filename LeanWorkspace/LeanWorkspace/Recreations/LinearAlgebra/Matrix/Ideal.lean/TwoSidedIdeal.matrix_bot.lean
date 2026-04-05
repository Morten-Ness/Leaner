import Mathlib

variable {R : Type*} (n : Type*)

variable [NonUnitalNonAssocRing R] [Fintype n]

theorem matrix_bot : (⊥ : TwoSidedIdeal R).matrix n = ⊥ := ringCon_injective <| RingCon.matrix_bot _

