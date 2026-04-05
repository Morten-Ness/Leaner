import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem mapMatrixModule_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (v : ι → M) :
    (g ∘ₗ f).mapMatrixModule ι v =
      g.mapMatrixModule ι (f.mapMatrixModule ι v) := by
  simp [LinearMap.mapMatrixModule_comp]

