import Mathlib

variable {R S : CommRingCat.{u}}

theorem toAlgHom_id (A : Under R) : CommRingCat.toAlgHom (𝟙 A) = AlgHom.id R A := rfl

