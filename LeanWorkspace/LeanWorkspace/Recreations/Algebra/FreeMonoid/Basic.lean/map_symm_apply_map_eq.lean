import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_symm_apply_map_eq {x : FreeMonoid α} (e : α ≃ β) :
    (FreeMonoid.map ⇑e.symm) ((FreeMonoid.map ⇑e) x) = x := by simp [FreeMonoid.map_map]

