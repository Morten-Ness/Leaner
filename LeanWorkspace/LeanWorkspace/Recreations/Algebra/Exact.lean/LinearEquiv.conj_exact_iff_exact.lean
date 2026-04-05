import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') :
    Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' →ₗ[R] N)) ↔ Exact f g := by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← Submodule.map_equiv_eq_comap_symm,
    LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

