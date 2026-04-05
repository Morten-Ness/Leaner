import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem prod_set' (L : List G) (n : ℕ) (a : G) :
    (L.set n a).prod = L.prod * if hn : n < L.length then L[n]⁻¹ * a else 1 := by
  refine (List.prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, List.prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, List.prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp (disch := grind) [take_of_length_le, drop_eq_nil_of_le]

