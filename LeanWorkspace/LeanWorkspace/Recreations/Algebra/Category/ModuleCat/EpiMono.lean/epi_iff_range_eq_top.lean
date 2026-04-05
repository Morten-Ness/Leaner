import Mathlib

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤ := ⟨fun _ => ModuleCat.range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| by convert LinearMap.range_eq_top.1 hf⟩

