import Mathlib

open scoped Pointwise

variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ := ⟨fun _ => CommGrpCat.ker_eq_bot_of_mono f, fun GrpCat.SurjectiveOfEpiAuxs.h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f.hom).1 GrpCat.SurjectiveOfEpiAuxs.h⟩

