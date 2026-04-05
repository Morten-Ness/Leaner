import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

theorem toSubmodule_inj {s t : NonUnitalSubalgebra R A} : s.toSubmodule = t.toSubmodule ↔ s = t := NonUnitalSubalgebra.toSubmodule_injective.eq_iff

