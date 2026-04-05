import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.congr_fun {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (x) : Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) := LinearMap.congr_fun h x

