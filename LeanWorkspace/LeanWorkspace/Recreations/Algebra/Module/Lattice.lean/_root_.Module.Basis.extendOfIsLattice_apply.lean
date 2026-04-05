import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem _root_.Module.Basis.extendOfIsLattice_apply [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [Submodule.IsLattice K M] (b : Module.Basis κ R M) (k : κ) :
    b.extendOfIsLattice K k = (b k).val := by
  simp [Module.Basis.extendOfIsLattice]

