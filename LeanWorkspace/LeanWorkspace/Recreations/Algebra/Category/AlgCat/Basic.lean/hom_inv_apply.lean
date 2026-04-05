import Mathlib

variable (R : Type u) [CommRing R]

theorem hom_inv_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp

