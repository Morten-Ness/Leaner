import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

theorem Projective.of_basis {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsuppSum]
  exact b.linearCombination_repr m

