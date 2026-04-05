import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

theorem natDegree_eq_one : p.natDegree = 1 ↔ ∃ a ≠ 0, ∃ b, Polynomial.C a * Polynomial.X + Polynomial.C b = p := by
  refine ⟨fun hp ↦ ⟨p.coeff 1, fun h ↦ ?_, p.coeff 0, ?_⟩, ?_⟩
  · rw [← hp, coeff_natDegree, leadingCoeff_eq_zero] at h
    simp_all
  · ext n
    obtain _ | _ | n := n
    · simp
    · simp
    · simp only [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      rw [coeff_eq_zero_of_natDegree_lt]
      simp [hp]
  · rintro ⟨a, ha, b, rfl⟩
    simp [ha]

