import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem vars_bind₁ [DecidableEq τ] (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (MvPolynomial.bind₁ f φ).vars ⊆ φ.vars.biUnion fun i => (f i).vars := by
  calc (MvPolynomial.bind₁ f φ).vars
    _ = (φ.support.sum fun x : σ →₀ ℕ => (MvPolynomial.bind₁ f) (monomial x (coeff x φ))).vars := by
      rw [← map_sum, ← φ.as_sum]
    _ ≤ φ.support.biUnion fun i : σ →₀ ℕ => ((MvPolynomial.bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUnion fun d : σ →₀ ℕ => vars (C (coeff d φ) * ∏ i ∈ d.support, f i ^ d i) := by
      simp only [MvPolynomial.bind₁_monomial]
    _ ≤ φ.support.biUnion fun d : σ →₀ ℕ => d.support.biUnion fun i => vars (f i) := ?_
    -- proof below
    _ ≤ φ.vars.biUnion fun i : σ => vars (f i) := ?_
    -- proof below
  · apply Finset.biUnion_mono
    intro d _hd
    calc
      vars (C (coeff d φ) * ∏ i ∈ d.support, f i ^ d i) ≤
          (C (coeff d φ)).vars ∪ (∏ i ∈ d.support, f i ^ d i).vars :=
        vars_mul _ _
      _ ≤ (∏ i ∈ d.support, f i ^ d i).vars := by
        simp only [Finset.empty_union, vars_C, Finset.le_iff_subset, Finset.Subset.refl]
      _ ≤ d.support.biUnion fun i : σ => vars (f i ^ d i) := vars_prod _
      _ ≤ d.support.biUnion fun i : σ => (f i).vars := ?_
    apply Finset.biUnion_mono
    intro i _hi
    apply vars_pow
  · intro j
    simp_rw [Finset.mem_biUnion]
    rintro ⟨d, hd, ⟨i, hi, hj⟩⟩
    exact ⟨i, (mem_vars _).mpr ⟨d, hd, hi⟩, hj⟩

