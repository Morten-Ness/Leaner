import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := ⟨fun _ => GrpCat.surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩

