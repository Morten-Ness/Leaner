import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

theorem exact_map_mkQ_range (f : M →ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) := LinearMap.exact_iff.mpr <| Submodule.ker_mkQ _

