import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem comp_X_add_C (hp : p.Monic) (r : R) : (Polynomial.Monic.comp p (Polynomial.X + Polynomial.C r)).Monic := by
  nontriviality R
  refine Polynomial.Monic.comp hp (Polynomial.monic_X_add_C _) fun ha ↦ ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha

