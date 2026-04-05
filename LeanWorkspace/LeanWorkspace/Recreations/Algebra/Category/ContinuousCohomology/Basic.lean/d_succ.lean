import Mathlib

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem d_succ (n : ℕ) :
    ContinuousCohomology.MultiInd.d R G (n + 1) = whiskerLeft (ContinuousCohomology.MultiInd.functor R G (n + 1)) (ContinuousCohomology.const R G) -
      (by exact whiskerRight (ContinuousCohomology.MultiInd.d R G n) (ContinuousCohomology.I R G)) := rfl

