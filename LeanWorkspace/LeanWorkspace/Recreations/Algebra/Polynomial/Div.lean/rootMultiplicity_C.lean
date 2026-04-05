import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem rootMultiplicity_C (r a : R) : Polynomial.rootMultiplicity a (Polynomial.C r) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (Polynomial.C r) 0, Polynomial.rootMultiplicity_zero]
  classical
  rw [Polynomial.rootMultiplicity_eq_multiplicity]
  split_ifs with hr
  · rfl
  have h : natDegree (Polynomial.C r) < natDegree (Polynomial.X - Polynomial.C a) := by simp
  simp_rw [multiplicity_eq_zero.mpr ((Polynomial.monic_X_sub_C a).not_dvd_of_natDegree_lt hr h)]

