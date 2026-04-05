import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem Fintype.prod_apply {α : Type*} {M : α → Type*} [Fintype ι] [∀ a, CommMonoid (M a)] (a : α)
    (g : ι → ∀ a, M a) : (∏ c, g c) a = ∏ c, g c a := Finset.prod_apply a Finset.univ g

