import Mathlib

open scoped Pointwise

variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ := ⟨fun _ => CommGrpCat.range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| show Function.Surjective f.hom from
      MonoidHom.range_eq_top.mp hf⟩

