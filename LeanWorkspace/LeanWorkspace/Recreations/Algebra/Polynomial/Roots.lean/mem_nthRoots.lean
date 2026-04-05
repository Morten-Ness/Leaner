import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_nthRoots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ Polynomial.nthRoots n a ↔ x ^ n = a := by
  rw [Polynomial.nthRoots, Polynomial.mem_roots (X_pow_sub_C_ne_zero hn a), IsRoot.def, eval_sub, eval_C, eval_pow,
    eval_X, sub_eq_zero]

