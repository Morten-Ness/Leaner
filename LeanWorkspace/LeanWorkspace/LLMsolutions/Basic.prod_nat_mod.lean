import Mathlib

variable {F ι κ G M N O : Type*}

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [Nat.mul_mod, ih]
      simp
