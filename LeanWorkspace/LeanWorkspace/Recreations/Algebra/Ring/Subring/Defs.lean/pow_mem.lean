import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem pow_mem {R : Type*} [Ring R] (s : Subring R) {x : R} (hx : x ∈ s) (n : ℕ) :
    x ^ n ∈ s := pow_mem hx n

