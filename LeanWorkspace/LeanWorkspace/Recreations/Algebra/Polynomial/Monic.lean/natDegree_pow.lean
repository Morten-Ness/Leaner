import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_pow (hp : p.Monic) (n : ℕ) : (p ^ n).natDegree = n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, Polynomial.Monic.natDegree_mul (hp.pow n) hp, hn, Nat.succ_mul, add_comm]

