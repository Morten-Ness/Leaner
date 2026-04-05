import Mathlib

variable {R A : Type*} [Semiring R]

variable [StarAddMonoid R] [Star A] {a : A}

variable [AddCommMonoid A] [Mul A] [SMulWithZero R A]

theorem isStarNormal_inr : IsStarNormal (a : Unitization R A) ↔ IsStarNormal a := by
  simp only [isStarNormal_iff, commute_iff_eq, ← Unitization.inr_star, ← Unitization.inr_mul, Unitization.inr_injective.eq_iff]

alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

