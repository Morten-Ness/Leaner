import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

theorem freeYonedaEquiv_comp {M N : PresheafOfModules.{v} R} {X : C}
    (m : ((free R).obj (yoneda.obj X) ⟶ M)) (φ : M ⟶ N) :
    PresheafOfModules.freeYonedaEquiv (m ≫ φ) = φ.app _ (PresheafOfModules.freeYonedaEquiv m) := rfl

