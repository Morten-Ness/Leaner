import Mathlib

open scoped ArithmeticFunction

theorem dvd_of_mem_finMulAntidiag {n d : ℕ} {f : Fin d → ℕ} (hf : f ∈ Nat.finMulAntidiag d n)
    (i : Fin d) : f i ∣ n := by
  rw [Nat.mem_finMulAntidiag] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (Finset.mem_univ i)

