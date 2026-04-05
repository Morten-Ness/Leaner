import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeffs_add [DecidableEq R] {p q : MvPolynomial σ R} (h : Disjoint p.support q.support) :
    (p + q).coeffs = p.coeffs ∪ q.coeffs := by
  ext r
  simp only [MvPolynomial.mem_coeffs_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ →₀ ℕ) (hne : p.coeff n ≠ 0) : q.coeff n = 0 :=
    MvPolynomial.notMem_support_iff.mp <| h.notMem_of_mem_left_finset (MvPolynomial.mem_support_iff.mpr hne)
  have hr (n : σ →₀ ℕ) (hne : q.coeff n ≠ 0) : p.coeff n = 0 :=
    MvPolynomial.notMem_support_iff.mp <| h.notMem_of_mem_right_finset (MvPolynomial.mem_support_iff.mpr hne)
  have hor (n) (h : ¬MvPolynomial.coeff n p + MvPolynomial.coeff n q = 0) : MvPolynomial.coeff n p ≠ 0 ∨ MvPolynomial.coeff n q ≠ 0 := by
    by_cases hp : MvPolynomial.coeff n p = 0 <;> simp_all
  refine ⟨fun ⟨n, hn1, hn2⟩ ↦ ?_, ?_⟩
  · obtain (h | h) := hor n hn1
    · exact Or.inl ⟨n, by simp [h, hn2, hl n h]⟩
    · exact Or.inr ⟨n, by simp [h, hn2, hr n h]⟩
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · exact ⟨n, by simp [hl n hn, hn]⟩
    · exact ⟨n, by simp [hr n hn, hn]⟩

