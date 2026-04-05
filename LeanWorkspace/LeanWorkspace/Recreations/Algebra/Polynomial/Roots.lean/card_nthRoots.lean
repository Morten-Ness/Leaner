import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_nthRoots (n : ℕ) (a : R) : Multiset.card (Polynomial.nthRoots n a) ≤ n := by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [Polynomial.nthRoots, Polynomial.roots, h, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (Polynomial.card_roots h)
          (by
            rw [hn, pow_zero, ← C_1, ← map_sub]
            exact degree_C_le))
  else by
    rw [← Nat.cast_le (α := WithBot ℕ)]
    rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
    exact Polynomial.card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))

