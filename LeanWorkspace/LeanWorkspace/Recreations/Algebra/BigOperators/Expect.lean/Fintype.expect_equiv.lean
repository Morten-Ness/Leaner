import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ i, f i = g (e i)) :
    𝔼 i, f i = 𝔼 i, g i := Fintype.expect_bijective _ e.bijective f g h

