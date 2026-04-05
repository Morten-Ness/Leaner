import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mclosure_range (f : F) : closure (Set.range f) = MonoidHom.mrange f := by
  rw [← Set.image_univ, ← MonoidHom.map_mclosure, MonoidHom.mrange_eq_map, closure_univ]

