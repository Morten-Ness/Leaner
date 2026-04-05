import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (Polynomial.C a * p).natDegree = p.natDegree := le_antisymm (Polynomial.natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (Polynomial.C ai * (Polynomial.C a * p)).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ ≤ (Polynomial.C a * p).natDegree := Polynomial.natDegree_C_mul_le ai (Polynomial.C a * p))

