import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem exists_fin_rename (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (f : Fin n → σ) (_hf : Function.Injective f) (q : MvPolynomial (Fin n) R), p = MvPolynomial.rename f q := by
  obtain ⟨s, q, rfl⟩ := MvPolynomial.exists_finset_rename p
  let n := Fintype.card { x // x ∈ s }
  let e := Fintype.equivFin { x // x ∈ s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, MvPolynomial.rename e q, ?_⟩
  rw [← MvPolynomial.rename_rename, MvPolynomial.rename_rename e]
  simp only [Function.comp_def, Equiv.symm_apply_apply, MvPolynomial.rename_rename]

