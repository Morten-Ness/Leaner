import Mathlib

open scoped Function

variable (R : Type*)

variable [Semiring R] (S : Sequence R)

theorem degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

