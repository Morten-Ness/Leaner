import Mathlib

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι → G}

variable [MulRightMono G]

theorem ciSup_mul (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a := (OrderIso.mulRight a).map_ciSup hf

