import Mathlib

variable {ι α β M N P G : Type*}

theorem sum_nat_mod (l : List ℕ) (n : ℕ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)

