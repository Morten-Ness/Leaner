import Mathlib

open scoped ArithmeticFunction

theorem ne_zero_of_mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ Nat.finMulAntidiag d n) (i : Fin d) : f i ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.mem_finMulAntidiag.mp hf).2 (Nat.dvd_of_mem_finMulAntidiag hf i)

