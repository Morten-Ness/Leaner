import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem Finset.prod_fn {α : Type*} {M : α → Type*} {ι} [∀ a, CommMonoid (M a)] (s : Finset ι)
    (g : ι → ∀ a, M a) : ∏ c ∈ s, g c = fun a ↦ ∏ c ∈ s, g c a := funext fun _ ↦ Finset.prod_apply _ _ _

