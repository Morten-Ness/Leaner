import Mathlib

variable {M : Type*} [Monoid M]

theorem Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
  fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

