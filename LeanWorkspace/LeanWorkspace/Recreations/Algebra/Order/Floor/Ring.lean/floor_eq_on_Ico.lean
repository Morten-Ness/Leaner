import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_eq_on_Ico (n : ℤ) : ∀ a ∈ Set.Ico (n : R) (n + 1), ⌊a⌋ = n := fun _ ⟨h₀, h₁⟩ =>
  Int.floor_eq_iff.mpr ⟨h₀, h₁⟩

