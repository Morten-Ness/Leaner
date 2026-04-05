import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

variable (hb : Submodule.span R (Set.range b) = ⊤)

theorem Matrix.isRepresentation.eq_toEnd_of_represents (A : Matrix.isRepresentation R b)
    {f : Module.End R M} (h : (A : Matrix ι ι R).Represents b f) :
    Matrix.isRepresentation.toEnd R b hb A = f := A.2.choose_spec.eq hb h

