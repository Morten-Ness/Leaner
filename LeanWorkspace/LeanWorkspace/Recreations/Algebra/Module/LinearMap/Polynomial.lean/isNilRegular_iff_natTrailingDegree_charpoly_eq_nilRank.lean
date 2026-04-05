import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

variable [Module.Finite R L] [Module.Free R L]

variable (x : L)

theorem isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] :
    LinearMap.IsNilRegular φ x ↔ (φ x).charpoly.natTrailingDegree = LinearMap.nilRank φ := by
  rw [LinearMap.isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (LinearMap.nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _).ne_zero

