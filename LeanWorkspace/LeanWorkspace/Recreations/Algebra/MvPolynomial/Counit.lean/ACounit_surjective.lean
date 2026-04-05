import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem ACounit_surjective : Function.Surjective (MvPolynomial.ACounit A B) := fun b => ⟨X b, MvPolynomial.ACounit_X A b⟩

