import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem ceil_intCast {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (z : ℤ) :
    ⌈(z : R)⌉₊ = z.toNat := eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

