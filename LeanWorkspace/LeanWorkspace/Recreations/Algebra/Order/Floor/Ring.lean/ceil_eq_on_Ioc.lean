import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : R) z, ⌈a⌉ = z := fun _ ⟨h₀, h₁⟩ =>
  Int.ceil_eq_iff.mpr ⟨h₀, h₁⟩

