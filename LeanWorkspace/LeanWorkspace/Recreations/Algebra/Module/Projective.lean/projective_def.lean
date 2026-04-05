import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem projective_def :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (linearCombination R id) s := ⟨fun h => h.1, fun h => ⟨h⟩⟩

