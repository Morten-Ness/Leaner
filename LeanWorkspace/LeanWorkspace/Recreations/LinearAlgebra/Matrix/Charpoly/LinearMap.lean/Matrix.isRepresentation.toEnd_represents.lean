import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

variable (hb : Submodule.span R (Set.range b) = ⊤)

theorem Matrix.isRepresentation.toEnd_represents (A : Matrix.isRepresentation R b) :
    (A : Matrix ι ι R).Represents b (Matrix.isRepresentation.toEnd R b hb A) := A.2.choose_spec

