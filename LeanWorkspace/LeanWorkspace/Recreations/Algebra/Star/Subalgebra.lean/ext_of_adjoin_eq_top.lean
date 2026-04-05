import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

theorem ext_of_adjoin_eq_top {s : Set A} (h : StarAlgebra.adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.EqOn f g) : f = g := DFunLike.ext f g fun _x => StarAlgHom.adjoin_le_equalizer f g hs <| h.symm ▸ trivial

