import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Function.Surjective.comp_exact_iff_exact {p : M' →ₗ[R] M} (h : Function.Surjective p) :
    Exact (f ∘ₗ p) g ↔ Exact f g := iff_of_eq <| forall_congr fun x =>
    congrArg (g x = 0 ↔ x ∈ ·) (h.range_comp f)

