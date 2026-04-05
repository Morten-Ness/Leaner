import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_smul {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S] [Fintype ι]
    [DecidableEq ι] (x : S) (b : Module.Basis ι R₁ S) (w : ι → S) :
    (b.toMatrix (x • w)) = (Algebra.leftMulMatrix b x) * (b.toMatrix w) := by
  ext
  rw [Module.Basis.toMatrix_apply, Pi.smul_apply, smul_eq_mul, ← Algebra.leftMulMatrix_mulVec_repr]
  rfl

