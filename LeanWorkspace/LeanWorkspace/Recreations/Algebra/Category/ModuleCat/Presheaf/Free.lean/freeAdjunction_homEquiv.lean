import Mathlib

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}

theorem freeAdjunction_homEquiv : (PresheafOfModules.freeAdjunction R).homEquiv F G = PresheafOfModules.freeHomEquiv := by
  simp [PresheafOfModules.freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

