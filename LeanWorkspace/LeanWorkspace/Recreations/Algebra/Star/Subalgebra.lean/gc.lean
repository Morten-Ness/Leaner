import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem gc : GaloisConnection (StarAlgebra.adjoin R : Set A → StarSubalgebra R A) (↑) := by
  intro s S
  rw [← StarSubalgebra.toSubalgebra_le_iff, StarAlgebra.adjoin_toSubalgebra, Algebra.adjoin_le_iff, StarSubalgebra.coe_toSubalgebra]
  exact
    ⟨fun h => Set.subset_union_left.trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

