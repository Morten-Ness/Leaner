import Mathlib

section

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

theorem IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔ Projective (of R P) := ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

end

section

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

variable {M : ModuleCat.{v} R}

theorem projective_of_free {ι : Type w} (b : Module.Basis ι R M) : Projective M := have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

end
