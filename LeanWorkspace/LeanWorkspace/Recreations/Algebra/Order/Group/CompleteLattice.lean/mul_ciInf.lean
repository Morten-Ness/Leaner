import Mathlib

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι → G}

variable [MulLeftMono G]

theorem mul_ciInf (hf : BddBelow (Set.range f)) (a : G) : (a * ⨅ i, f i) = ⨅ i, a * f i := (OrderIso.mulLeft a).map_ciInf hf

