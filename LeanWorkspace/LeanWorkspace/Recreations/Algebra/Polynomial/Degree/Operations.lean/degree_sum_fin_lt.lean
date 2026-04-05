import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_sum_fin_lt {n : ℕ} (f : Fin n → R) :
    degree (∑ i : Fin n, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)) < n := (degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
      (degree_C_mul_X_pow_le _ _).trans_lt <| WithBot.coe_lt_coe.2 k.is_lt

