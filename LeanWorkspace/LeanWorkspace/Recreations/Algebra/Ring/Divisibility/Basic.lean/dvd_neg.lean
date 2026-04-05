import Mathlib

variable {α β : Type*}

variable [Semigroup α] [HasDistribNeg α] {a b : α}

theorem dvd_neg : a ∣ -b ↔ a ∣ b := (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]

