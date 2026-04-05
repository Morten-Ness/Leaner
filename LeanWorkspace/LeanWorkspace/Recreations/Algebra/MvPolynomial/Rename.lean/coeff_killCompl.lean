import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem coeff_killCompl {s} :
    (p.killCompl hf).coeff s = p.coeff (s.mapDomain f) := by
  classical
  apply p.induction_on' (P := fun p ↦ (p.killCompl hf).coeff s = p.coeff (s.mapDomain f))
  · intro u r
    rw [MvPolynomial.killCompl_monomial]
    split_ifs with h
    · simp [← (Finsupp.mapDomain_injective hf).eq_iff, u.mapDomain_comapDomain _ hf h]
    · simp? says simp only [coeff_zero, coeff_monomial, right_eq_ite_iff]
      intro rfl
      contrapose! h
      apply subset_trans <| SetLike.coe_subset_coe.mpr <| Finsupp.mapDomain_support
      simp
  · simp_intro ..

