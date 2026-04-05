import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem degree_eraseLead_lt (hf : f ≠ 0) : (Polynomial.eraseLead f).degree < f.degree := f.degree_erase_lt hf

