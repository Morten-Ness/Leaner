import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) :
    ⇑((Module.Basis.finTwoProd R).repr x) = ![x.fst, x.snd] := rfl

