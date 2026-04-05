import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R}

theorem fromFreeYoneda_app_apply (m : M.Elements) :
    m.fromFreeYoneda.app m.1 (ModuleCat.freeMk (𝟙 _)) = m.2 := by
  apply PresheafOfModules.freeYonedaEquiv_symm_app

