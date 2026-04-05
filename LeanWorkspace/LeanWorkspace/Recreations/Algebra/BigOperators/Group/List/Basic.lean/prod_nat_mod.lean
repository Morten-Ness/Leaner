import Mathlib

variable {ι α β M N P G : Type*}

theorem prod_nat_mod (l : List ℕ) (n : ℕ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)

