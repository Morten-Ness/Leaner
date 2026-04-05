import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Function.Injective.comp_exact_iff_exact {i : P →ₗ[R] P'} (h : Function.Injective i) :
    Exact f (i ∘ₗ g) ↔ Exact f g := forall_congr' fun _ => iff_congr (map_eq_zero_iff _ h) Iff.rfl

