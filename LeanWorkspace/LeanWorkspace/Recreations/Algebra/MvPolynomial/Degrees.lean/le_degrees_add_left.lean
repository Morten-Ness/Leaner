import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem le_degrees_add_left (h : Disjoint p.degrees q.degrees) : p.degrees ≤ (p + q).degrees := by
  classical
  apply Finset.sup_le
  intro d hd
  rw [Multiset.disjoint_iff_ne] at h
  obtain rfl | h0 := eq_or_ne d 0
  · rw [toMultiset_zero]; apply Multiset.zero_le
  · refine Finset.le_sup_of_le (b := d) ?_ le_rfl
    rw [mem_support_iff, coeff_add]
    suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
    rw [Ne, ← Finsupp.support_eq_empty, ← Ne, ← Finset.nonempty_iff_ne_empty] at h0
    obtain ⟨j, hj⟩ := h0
    contrapose! h
    rw [mem_support_iff] at hd
    refine ⟨j, ?_, j, ?_, rfl⟩
    all_goals rw [MvPolynomial.mem_degrees]; refine ⟨d, ?_, hj⟩; assumption

