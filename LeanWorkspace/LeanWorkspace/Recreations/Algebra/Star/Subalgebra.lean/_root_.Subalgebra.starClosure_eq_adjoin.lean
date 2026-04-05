import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem _root_.Subalgebra.starClosure_eq_adjoin (S : Subalgebra R A) :
    S.starClosure = StarAlgebra.adjoin R (S : Set A) := le_antisymm (Subalgebra.starClosure_le_iff.2 <| StarAlgebra.subset_adjoin R (S : Set A))
    (StarAlgebra.adjoin_le (le_sup_left : S ≤ S ⊔ star S))

