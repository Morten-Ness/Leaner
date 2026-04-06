import Mathlib

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹ := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      simp [ih, mul_comm, mul_left_comm, mul_assoc]
