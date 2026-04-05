import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_add_eq_left_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (p + q).totalDegree = p.totalDegree := by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact MvPolynomial.totalDegree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.mpr hp) fun m : σ →₀ ℕ =>
        Multiset.card (toMultiset m)
    have hb : b ∉ q.support := by
      contrapose! h
      rw [MvPolynomial.totalDegree_eq p, hb₂, MvPolynomial.totalDegree_eq]
      apply Finset.le_sup h
    have hbb : b ∈ (p + q).support := by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [MvPolynomial.totalDegree_eq, hb₂, MvPolynomial.totalDegree_eq]
    exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb

