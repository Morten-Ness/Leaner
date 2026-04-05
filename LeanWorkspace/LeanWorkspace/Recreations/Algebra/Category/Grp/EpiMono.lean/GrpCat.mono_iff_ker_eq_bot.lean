import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ := ⟨fun _ => GrpCat.ker_eq_bot_of_mono f, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

