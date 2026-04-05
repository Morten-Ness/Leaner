import Mathlib

variable {R : Type*} [CommRing R] [IsDomain R]

variable {σ : Type*} {p q : MvPolynomial σ R} (s : σ → Set R) (hs : ∀ i, (s i).Infinite)

private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (s : Fin n → Set R) (hs : ∀ i, (s i).Infinite)
    (h : ∀ x ∈ Set.pi .univ s, eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    rw [map_zero]
    convert h _ finZeroElim
  | succ n ih =>
    apply (finSuccEquiv R n).injective
    rw [map_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((hs 0).image (C_injective ..).injOn).mono
    rintro _ ⟨r, hr, rfl⟩
    refine ih (s ·.succ) (fun _ ↦ hs _) fun x hx ↦ ?_
    rw [eval_polynomial_eval_finSuccEquiv]
    exact h _ fun i _ ↦ i.cases (by simpa using hr) (by simpa using hx)


theorem funext_set_iff : p = q ↔ (∀ x ∈ Set.pi .univ s, eval x p = eval x q) := ⟨by rintro rfl _ _; rfl, MvPolynomial.funext_set s hs⟩

