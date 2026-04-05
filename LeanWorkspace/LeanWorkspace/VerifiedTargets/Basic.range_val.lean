import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

theorem range_val : S.val.range = S := Subalgebra.ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val

