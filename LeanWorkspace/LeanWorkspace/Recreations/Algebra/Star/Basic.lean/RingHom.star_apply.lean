import Mathlib

open scoped Ring

variable {R : Type u}

variable [CommSemiring R] [StarRing R]

theorem RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S →+* R) (s : S) :
    star f s = star (f s) := rfl

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply

alias RCLike.conj_conj := starRingEnd_self_apply

