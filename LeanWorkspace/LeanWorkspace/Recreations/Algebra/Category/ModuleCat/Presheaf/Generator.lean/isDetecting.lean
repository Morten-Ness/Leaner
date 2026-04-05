import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

theorem isDetecting : ObjectProperty.IsDetecting (PresheafOfModules.freeYoneda R) := (PresheafOfModules.freeYoneda.isSeparating R).isDetecting

