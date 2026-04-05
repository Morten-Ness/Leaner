import Mathlib

variable {F ι κ G M N O : Type*}

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

