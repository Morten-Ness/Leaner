import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem projective_def' :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Finsupp.linearCombination R id ∘ₗ s = .id := by
  simp_rw [Module.projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]

