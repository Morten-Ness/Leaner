import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem _root_.Polynomial.not_isUnit_X_add_C [Nontrivial R] (a : R) : ¬ IsUnit (Polynomial.X + Polynomial.C a) := by
  rintro ⟨⟨_, g, hfg, hgf⟩, rfl⟩
  have h := (Polynomial.monic_X_add_C a).natDegree_mul' (right_ne_zero_of_mul_eq_one hfg)
  rw [hfg, natDegree_one, natDegree_X_add_C] at h
  grind

