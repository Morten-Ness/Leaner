import Mathlib

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      simp [ih, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
