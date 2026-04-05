import Mathlib

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι → G}

variable [MulRightMono G]

theorem ciInf_mul (hf : BddBelow (Set.range f)) (a : G) : (⨅ i, f i) * a = ⨅ i, f i * a := (OrderIso.mulRight a).map_ciInf hf

