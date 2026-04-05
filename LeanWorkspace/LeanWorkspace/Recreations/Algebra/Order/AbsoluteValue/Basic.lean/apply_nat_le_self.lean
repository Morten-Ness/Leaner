import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

variable [IsDomain S] [Nontrivial R]

omit [Nontrivial R] in
theorem apply_nat_le_self [IsOrderedRing S] (n : ℕ) : abv n ≤ n := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.eq_zero (n : R)]
  induction n with
  | zero => simp
  | succ n ih =>
  · grw [Nat.cast_succ, Nat.cast_succ, AbsoluteValue.add_le abv, AbsoluteValue.map_one abv, ih]

