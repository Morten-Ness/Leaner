import Mathlib

theorem ofHom_injective {X Y : Type u} [CommGroup X] [CommGroup Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

-- We verify that simp lemmas apply when coercing morphisms to functions.

