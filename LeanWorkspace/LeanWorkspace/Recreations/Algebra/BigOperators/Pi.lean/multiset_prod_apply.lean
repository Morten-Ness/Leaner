import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem multiset_prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Multiset (∀ a, M a)) : s.prod a = (s.map fun f : ∀ a, M a ↦ f a).prod := (evalMonoidHom M a).map_multiset_prod _

