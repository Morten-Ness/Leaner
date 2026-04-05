import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_degree_le : (Polynomial.eraseLead f).degree ≤ f.degree := f.degree_erase_le _

