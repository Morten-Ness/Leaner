import Mathlib

variable (R : Type u) [CommRing R]

theorem id_apply (A : AlgCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

