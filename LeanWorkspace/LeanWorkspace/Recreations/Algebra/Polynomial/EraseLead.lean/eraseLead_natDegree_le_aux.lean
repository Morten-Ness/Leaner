import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_natDegree_le_aux : (Polynomial.eraseLead f).natDegree ≤ f.natDegree := natDegree_le_natDegree Polynomial.eraseLead_degree_le

