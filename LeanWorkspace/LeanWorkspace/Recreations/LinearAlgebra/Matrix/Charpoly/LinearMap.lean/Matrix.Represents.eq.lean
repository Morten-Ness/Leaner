import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.eq (hb : Submodule.span R (Set.range b) = ⊤)
    {A : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : A.Represents b f') : f = f' := PiToModule.fromEnd_injective R b hb (h.symm.trans h')

