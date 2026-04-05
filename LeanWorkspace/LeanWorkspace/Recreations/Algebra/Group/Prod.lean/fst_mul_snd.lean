import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p := Prod.ext (mul_one p.1) (one_mul p.2)

