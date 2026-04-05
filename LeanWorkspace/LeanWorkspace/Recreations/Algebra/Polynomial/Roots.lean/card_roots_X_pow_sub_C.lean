import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    Multiset.card (Polynomial.roots ((X : R[X]) ^ n - C a)) ≤ n := WithBot.coe_le_coe.1 <|
    calc
      (Multiset.card (Polynomial.roots ((X : R[X]) ^ n - C a)) : WithBot ℕ) ≤ degree ((X : R[X]) ^ n - C a) :=
        Polynomial.card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a

