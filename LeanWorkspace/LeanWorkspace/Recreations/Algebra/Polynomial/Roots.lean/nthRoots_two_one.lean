import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem nthRoots_two_one : Polynomial.nthRoots 2 (1 : R) = {-1,1} := by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X ^ 2 - C 1 : R[X]) ≠ 0 := fun h ↦ by simpa using congrArg (coeff · 0) h
  rw [Polynomial.nthRoots, h₁, Polynomial.roots_mul (h₁ ▸ h₂), Polynomial.roots_X_add_C, Polynomial.roots_X_sub_C]; rfl

