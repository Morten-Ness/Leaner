import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem MonicDegreeEq.coeff_of_ge (p : MonicDegreeEq R n) (i : ℕ) (hi : n ≤ i) :
    p.1.coeff i = if i = n then 1 else 0 := by
  split_ifs <;> simp_all [p.2.1, p.2.2 _ (hi.lt_of_ne (.symm _))]

