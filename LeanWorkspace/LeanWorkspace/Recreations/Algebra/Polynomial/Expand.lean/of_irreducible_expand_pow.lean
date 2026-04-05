import Mathlib

open scoped Polynomial

variable (R : Type u) [CommRing R] [IsDomain R]

theorem of_irreducible_expand_pow {p : ℕ} (hp : p ≠ 0) {f : R[X]} {n : ℕ} :
    Irreducible (Polynomial.expand R (p ^ n) f) → Irreducible f := Nat.recOn n (fun hf => by rwa [pow_zero, Polynomial.expand_one] at hf) fun n ih hf =>
    ih <| Polynomial.of_irreducible_expand hp <| by
      rw [pow_succ'] at hf
      rwa [Polynomial.expand_expand]

