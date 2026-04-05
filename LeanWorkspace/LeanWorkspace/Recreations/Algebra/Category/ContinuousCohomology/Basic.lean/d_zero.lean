import Mathlib

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem d_zero : ContinuousCohomology.MultiInd.d R G 0 = ContinuousCohomology.const R G := rfl

