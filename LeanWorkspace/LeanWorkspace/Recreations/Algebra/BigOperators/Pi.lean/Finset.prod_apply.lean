import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem Finset.prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι → ∀ a, M a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a := map_prod (Pi.evalMonoidHom M a) _ _

