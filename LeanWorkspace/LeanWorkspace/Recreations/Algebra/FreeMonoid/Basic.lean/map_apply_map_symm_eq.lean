import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_apply_map_symm_eq {x : FreeMonoid β} (e : α ≃ β) :
    (FreeMonoid.map ⇑e) ((FreeMonoid.map ⇑e.symm) x) = x := by simp [FreeMonoid.map_map]

