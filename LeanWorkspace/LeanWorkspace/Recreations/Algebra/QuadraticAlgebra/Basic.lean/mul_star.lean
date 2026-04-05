import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem mul_star (x y : R) :
    (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra R a b) = (algebraMap _ _ x) * (algebraMap _ _ x) +
      (algebraMap _ _ b) * (algebraMap _ _ x) * (algebraMap _ _ y) - (algebraMap _ _ a) *
      (algebraMap _ _ y) * (algebraMap _ _ y) := by
  ext <;> simp <;> ring

