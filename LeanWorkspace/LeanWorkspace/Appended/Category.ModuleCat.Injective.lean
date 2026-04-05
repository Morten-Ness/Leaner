import Mathlib

section

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) := ⟨fun _ => Module.injective_object_of_injective_module R M,
   fun _ => Module.injective_module_of_injective_object R M⟩

end

section

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

theorem injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g := by
    have : CategoryTheory.Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, h⟩ := inj.factors (ModuleCat.ofHom g) (ModuleCat.ofHom f)
    obtain rfl := ModuleCat.hom_ext_iff.mp h
    exact ⟨l.hom, fun _ => rfl⟩

end
