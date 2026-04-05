import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S]

theorem exists_rename_eq_of_vars_subset_range (p : MvPolynomial σ R) (f : τ → σ) (hfi : Function.Injective f)
    (hf : ↑p.vars ⊆ Set.range f) : ∃ q : MvPolynomial τ R, rename f q = p := ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
      change (rename f).toRingHom.comp _ p = RingHom.id _ p
      refine MvPolynomial.hom_congr_vars ?_ ?_ ?_
      · ext1
        simp [algebraMap_eq]
      · intro i hip _
        rcases hf hip with ⟨i, rfl⟩
        simp [partialInv_left hfi]
      · rfl⟩

