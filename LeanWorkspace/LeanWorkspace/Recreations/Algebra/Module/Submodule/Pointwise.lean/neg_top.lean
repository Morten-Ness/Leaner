import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_top : -(⊤ : Submodule R M) = ⊤ := SetLike.coe_injective <| Set.neg_univ

