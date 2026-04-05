import Mathlib

variable {ι α β M N P G : Type*}

variable [Group G]

theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹ := by
  simp [List.prod_inv_reverse]

