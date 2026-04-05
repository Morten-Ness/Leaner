import Mathlib

variable {α β : Type*}

variable [Semigroup α] [HasDistribNeg α] {a b : α}

theorem neg_dvd : -a ∣ b ↔ a ∣ b := (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg

