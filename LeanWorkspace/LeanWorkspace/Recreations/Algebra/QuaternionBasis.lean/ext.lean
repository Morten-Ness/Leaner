import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

theorem ext ⦃q₁ q₂ : QuaternionAlgebra.Basis A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
    (hj : q₁.j = q₂.j) : q₁ = q₂ := by
  cases q₁; cases q₂; grind

