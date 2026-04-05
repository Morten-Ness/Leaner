import Mathlib

theorem ofHom_injective {X Y : Type u} [Group X] [Group Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

