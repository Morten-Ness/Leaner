import Mathlib

variable (R : Type u) [CommRing R]

theorem inv_hom_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp

