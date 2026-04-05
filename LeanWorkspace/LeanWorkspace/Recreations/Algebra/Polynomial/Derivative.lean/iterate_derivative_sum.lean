import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_sum (k : ℕ) (s : Finset ι) (f : ι → R[X]) :
    Polynomial.derivative^[k] (∑ b ∈ s, f b) = ∑ b ∈ s, Polynomial.derivative^[k] (f b) := by
  simp_rw [← Module.End.pow_apply, map_sum]

