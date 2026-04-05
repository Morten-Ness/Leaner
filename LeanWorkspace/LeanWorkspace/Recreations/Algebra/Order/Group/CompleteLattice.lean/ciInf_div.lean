import Mathlib

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι → G}

variable [MulRightMono G]

theorem ciInf_div (hf : BddBelow (Set.range f)) (a : G) : (⨅ i, f i) / a = ⨅ i, f i / a := by
  simp only [div_eq_mul_inv, ciInf_mul hf]

