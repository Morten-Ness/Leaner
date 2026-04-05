import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_map {S : Type*} [Semiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).reflect n = (p.reflect n).map f := by
  ext; simp

