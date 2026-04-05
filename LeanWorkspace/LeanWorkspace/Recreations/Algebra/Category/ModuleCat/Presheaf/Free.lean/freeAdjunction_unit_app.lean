import Mathlib

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}

theorem freeAdjunction_unit_app :
    (PresheafOfModules.freeAdjunction R).unit.app F = PresheafOfModules.freeAdjunctionUnit R F := rfl

