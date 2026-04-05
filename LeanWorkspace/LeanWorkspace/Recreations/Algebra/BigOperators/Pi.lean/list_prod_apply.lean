import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem list_prod_apply {α : Type*} {M : α → Type*} [∀ a, Monoid (M a)] (a : α)
    (l : List (∀ a, M a)) : l.prod a = (l.map fun f : ∀ a, M a ↦ f a).prod := map_list_prod (evalMonoidHom M a) _

