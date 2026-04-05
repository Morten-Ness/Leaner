import Mathlib

section

variable (R : Type u) [Ring R]

theorem ModuleCat.isSeparator [Small.{v} R] : IsSeparator (ModuleCat.of.{v} R (Shrink.{v} R)) := fun X Y f g h ↦ by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp
    (Shrink.linearEquiv R R : Shrink R →ₗ[R] R))) 1

end
