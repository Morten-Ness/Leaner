import Mathlib

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

theorem IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔ Projective (of R P) := ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

