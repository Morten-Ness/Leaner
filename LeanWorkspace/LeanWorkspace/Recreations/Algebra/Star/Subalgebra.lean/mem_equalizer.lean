import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

variable [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] (f g : F)

theorem mem_equalizer (x : A) : x ∈ StarAlgHom.equalizer f g ↔ f x = g x := Iff.rfl

