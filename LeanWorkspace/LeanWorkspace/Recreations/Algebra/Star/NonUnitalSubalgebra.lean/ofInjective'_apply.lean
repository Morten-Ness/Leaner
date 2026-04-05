import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [Module R A] [Star A]

variable [NonUnitalSemiring B] [Module R B] [Star B]

variable [NonUnitalSemiring C] [Module R C] [Star C]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

theorem ofInjective'_apply (f : F) (hf : Function.Injective f) (x : A) :
    StarAlgEquiv.ofInjective' f hf x = f x := rfl

