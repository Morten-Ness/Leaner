import Mathlib

open scoped ArithmeticFunction

theorem prod_eq_of_mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ Nat.finMulAntidiag d n) : ∏ i, f i = n := (Nat.mem_finMulAntidiag.mp hf).1

