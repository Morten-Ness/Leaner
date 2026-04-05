import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.degree_eq_one_of_irreducible {f : R[X]} (hf : Polynomial.Splits f)
    (h : Irreducible f) : degree f = 1 := le_antisymm (hf.degree_le_one_of_irreducible h)
    ((WithBot.one_le_iff_pos _).mpr (degree_pos_of_irreducible h))

