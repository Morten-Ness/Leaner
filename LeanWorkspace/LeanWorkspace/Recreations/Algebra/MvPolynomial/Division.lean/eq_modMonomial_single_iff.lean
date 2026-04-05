import Mathlib

variable {σ R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

theorem eq_modMonomial_single_iff (h : X i ∣ p - r) :
    r = p.modMonomial (Finsupp.single i 1) ↔
      ∀ n ∈ r.support, n i = 0 := by
  refine ⟨fun h n ↦ ?_, fun hr ↦ ?_⟩
  · contrapose!
    intro hn
    rw [h, notMem_support_iff]
    apply MvPolynomial.coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply MvPolynomial.eq_modMonomial_single (q := q) _ hr
    rwa [← sub_eq_iff_eq_add]

