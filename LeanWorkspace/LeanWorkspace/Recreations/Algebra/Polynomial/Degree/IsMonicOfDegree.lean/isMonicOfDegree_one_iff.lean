import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_one_iff {f : R[X]} : IsMonicOfDegree f 1 ↔ ∃ r : R, f = X + C r := by
  refine ⟨fun H ↦ ?_, fun ⟨r, H⟩ ↦ H ▸ Polynomial.isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (Polynomial.isMonicOfDegree_X_add_one _) (by lia)

