import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem exists_finset_rename (p : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q : MvPolynomial { x // x ∈ s } R), p = MvPolynomial.rename (↑) q := by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [MvPolynomial.rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine ⟨s ∪ t, ⟨?_, ?_⟩⟩
    · refine MvPolynomial.rename (Subtype.map id ?_) p + MvPolynomial.rename (Subtype.map id ?_) q <;>
        simp +contextual only [id, true_or, or_true,
          Finset.mem_union, forall_true_iff]
    · simp only [MvPolynomial.rename_rename, map_add]
      rfl
  · rintro p n ⟨s, p, rfl⟩
    refine ⟨insert n s, ⟨?_, ?_⟩⟩
    · refine MvPolynomial.rename (Subtype.map id ?_) p * X ⟨n, s.mem_insert_self n⟩
      simp +contextual only [id, or_true, Finset.mem_insert, forall_true_iff]
    · simp only [MvPolynomial.rename_rename, MvPolynomial.rename_X, map_mul]
      rfl

