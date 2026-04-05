import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [Module R A] [Star A]

variable [NonUnitalSemiring B] [Module R B] [Star B]

variable [NonUnitalSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem ofLeftInverse'_apply {g : B → A} {f : F} (h : Function.LeftInverse g f) (x : A) :
    StarAlgEquiv.ofLeftInverse' h x = f x := rfl

