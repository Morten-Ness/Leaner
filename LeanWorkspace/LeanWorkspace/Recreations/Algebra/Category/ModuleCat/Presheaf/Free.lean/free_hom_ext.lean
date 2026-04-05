import Mathlib

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}

theorem free_hom_ext {ψ ψ' : PresheafOfModules.freeObj F ⟶ G}
    (h : PresheafOfModules.freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _ =
      PresheafOfModules.freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ') _) : ψ = ψ' := PresheafOfModules.freeHomEquiv.injective h

