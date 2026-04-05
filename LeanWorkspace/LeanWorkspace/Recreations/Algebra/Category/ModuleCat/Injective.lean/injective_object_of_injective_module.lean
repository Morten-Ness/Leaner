import Mathlib

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

theorem injective_object_of_injective_module [inj : Function.Injective R M] :
    CategoryTheory.Injective (ModuleCat.of R M) where
  factors g f m := have ⟨l, h⟩ := inj.out f.hom ((ModuleCat.mono_iff_injective f).mp m) g.hom
    ⟨ModuleCat.ofHom l, by ext x; simpa using h x⟩

