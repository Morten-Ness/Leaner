import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_mul_self_nonneg (r : R) : 0 ≤ star r * r := StarOrderedRing.nonneg_iff.mpr <| AddSubmonoid.subset_closure ⟨r, rfl⟩

