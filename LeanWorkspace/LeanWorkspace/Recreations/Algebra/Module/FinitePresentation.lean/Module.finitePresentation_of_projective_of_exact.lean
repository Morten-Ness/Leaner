import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem Module.finitePresentation_of_projective_of_exact
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R N] [Module.Projective R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.FinitePresentation R M := have ⟨l, hl⟩ := Module.projective_lifting_property g .id hg
  Module.finitePresentation_of_split_exact f g l hl hf H

