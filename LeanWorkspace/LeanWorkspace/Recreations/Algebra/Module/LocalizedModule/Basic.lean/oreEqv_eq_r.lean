import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

theorem oreEqv_eq_r : (OreLocalization.oreEqv S M).r = LocalizedModule.r S M := by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm, mul_smul, ← h₁, mul_comm, mul_smul, Submonoid.smul_def]
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul, ← hu, mul_smul, Submonoid.coe_mul, mul_assoc, mul_assoc, mul_comm (a.2 : R)]
    simp [Submonoid.smul_def]

