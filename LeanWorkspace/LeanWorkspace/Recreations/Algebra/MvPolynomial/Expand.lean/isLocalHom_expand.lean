import Mathlib

variable (R σ : Type*) [CommRing R]

theorem isLocalHom_expand {p : ℕ} (hp : p ≠ 0) : IsLocalHom (MvPolynomial.expand p (R := R) (σ := σ)) := by
  refine ⟨fun f hf => ?_⟩
  rw [MvPolynomial.isUnit_iff] at hf ⊢
  simp only [MvPolynomial.coeff_expand_zero p hp] at hf
  refine ⟨hf.1, fun i hi ↦ ?_⟩
  rw [← MvPolynomial.coeff_expand_smul p hp]
  apply hf.2
  simp [hi, hp]

