import Mathlib

variable {M : Type*} [Monoid M]

theorem Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
  fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

