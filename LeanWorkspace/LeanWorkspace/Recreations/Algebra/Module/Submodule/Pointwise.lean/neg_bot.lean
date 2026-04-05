import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_bot : -(⊥ : Submodule R M) = ⊥ := SetLike.coe_injective <| (Set.neg_singleton 0).trans <| congr_arg _ neg_zero

