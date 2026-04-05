import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem nextCoeff_map {f : R →+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).nextCoeff = f p.nextCoeff := by
  simp only [hf, nextCoeff, Polynomial.natDegree_map_eq_of_injective]
  split_ifs <;> simp

