import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem toMatrix_map_vecMul {S : Type*} [Semiring S] [Algebra R S] [Fintype ι] (b : Module.Basis ι R S)
    (v : ι' → S) : b ᵥ* ((b.toMatrix v).map <| algebraMap R S) = v := by
  ext i
  simp_rw [vecMul, dotProduct, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    Module.Basis.sum_toMatrix_smul_self]

