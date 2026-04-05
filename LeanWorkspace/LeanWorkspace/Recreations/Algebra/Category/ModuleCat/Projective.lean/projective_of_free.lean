import Mathlib

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

variable {M : ModuleCat.{v} R}

theorem projective_of_free {ι : Type w} (b : Module.Basis ι R M) : Projective M := have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

