import Mathlib

variable {F ι κ G M N O : Type*}

theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      simp [Multiset.sum_cons, Nat.add_mod, ih]
