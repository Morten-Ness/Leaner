import Mathlib

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι → G}

variable [MulRightMono G]

theorem ciSup_div (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, ciSup_mul hf]

