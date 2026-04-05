import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

theorem toSubmodule_injective : (toSubmodule : NonUnitalSubalgebra R A → Submodule R A).Injective := fun _ _ h ↦ SetLike.ext (SetLike.ext_iff.mp h :)

