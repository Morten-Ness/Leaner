import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

theorem adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : StarAlgebra.adjoin R s ≤ StarAlgHom.equalizer f g := StarAlgebra.adjoin_le h

