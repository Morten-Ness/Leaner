import Mathlib

variable (R : Type u) [CommRing R]

theorem comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

