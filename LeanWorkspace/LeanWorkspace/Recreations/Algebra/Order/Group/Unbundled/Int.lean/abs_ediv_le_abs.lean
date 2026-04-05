import Mathlib

theorem abs_ediv_le_abs : ∀ a b : ℤ, |a / b| ≤ |a| := suffices ∀ (a : ℤ) (n : ℕ), |a / n| ≤ |a| from fun a b =>
    match b, Int.eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le
    (match a, n with
      | (m : ℕ), n => Nat.div_le_self _ _
      | -[m+1], 0 => Nat.zero_le _
      | -[m+1], n + 1 => Nat.succ_le_succ (Nat.div_le_self _ _))

