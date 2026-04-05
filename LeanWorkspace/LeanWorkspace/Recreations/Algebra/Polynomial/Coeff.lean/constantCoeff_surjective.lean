import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem constantCoeff_surjective : Function.Surjective (Polynomial.constantCoeff (R := R)) :=
  fun x ↦ ⟨Polynomial.C x, by simp⟩

