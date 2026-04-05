import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * Polynomial.C a).natDegree = p.natDegree := le_antisymm (Polynomial.natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * Polynomial.C a * Polynomial.C ai).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ ≤ (p * Polynomial.C a).natDegree := Polynomial.natDegree_mul_C_le (p * Polynomial.C a) ai)

