import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem pow_mem {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x ∈ s)
    (n : ℕ) : x ^ n ∈ s := pow_mem hx n

