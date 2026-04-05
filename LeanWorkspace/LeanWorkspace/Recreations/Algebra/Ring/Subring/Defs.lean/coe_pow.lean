import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_pow {R} [Ring R] (s : Subring R) (x : s) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n := SubmonoidClass.coe_pow x n

