import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_mul_X_eq_degreeOf_add_one_iff (j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf j (f * X j) = MvPolynomial.degreeOf j f + 1 ↔ f ≠ 0 := by
  refine ⟨fun h => by by_contra ha; simp [ha] at h, fun h => ?_⟩
  apply Nat.le_antisymm (MvPolynomial.degreeOf_mul_X_self j f)
  have : (f.support.sup fun m ↦ m j) + 1 = (f.support.sup fun m ↦ (m j + 1)) :=
    Finset.comp_sup_eq_sup_comp_of_nonempty @Nat.succ_le_succ (support_nonempty.mpr h)
  simp only [MvPolynomial.degreeOf_eq_sup, support_mul_X, this]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.sup_map, bot_eq_zero', add_pos_iff, zero_lt_one, or_true, Finset.le_sup_iff]
  use x
  simpa using mem_support_iff.mp hx

