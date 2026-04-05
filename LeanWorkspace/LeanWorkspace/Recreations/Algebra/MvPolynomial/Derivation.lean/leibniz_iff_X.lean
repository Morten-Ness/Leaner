import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

variable [IsScalarTower R (MvPolynomial σ R) A]

theorem leibniz_iff_X (D : MvPolynomial σ R →ₗ[R] A) (h₁ : D 1 = 0) :
    (∀ p q, D (p * q) = p • D q + q • D p) ↔ ∀ s i, D (monomial s 1 * X i) =
    (monomial s 1 : MvPolynomial σ R) • D (X i) + (X i : MvPolynomial σ R) • D (monomial s 1) := by
  refine ⟨fun H p i => H _ _, fun H => ?_⟩
  have hC : ∀ r, D (C r) = 0 := by intro r; rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : ∀ p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction p using MvPolynomial.induction_on' with
    | monomial s r =>
      rw [← mul_one r, ← C_mul_monomial, mul_assoc, C_mul', D.map_smul, H, C_mul', smul_assoc,
        smul_add, D.map_smul, smul_comm r (X i)]
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_smul, smul_add, add_add_add_comm]
  intro p q
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [mul_comm, C_mul', hC, smul_zero, zero_add, D.map_smul, C_eq_smul_one, smul_one_smul]
  | add q₁ q₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]; abel
  | mul_X q i hq =>
    simp only [this, ← mul_assoc, hq, mul_smul, smul_add, add_assoc]
    rw [smul_comm (X i), smul_comm (X i)]

