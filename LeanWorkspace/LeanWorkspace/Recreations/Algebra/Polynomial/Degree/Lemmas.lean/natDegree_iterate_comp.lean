import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

variable [NoZeroDivisors R]

theorem natDegree_iterate_comp (k : ℕ) :
    (p.comp^[k] q).natDegree = p.natDegree ^ k * q.natDegree := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Polynomial.natDegree_comp, IH, pow_succ', mul_assoc]

