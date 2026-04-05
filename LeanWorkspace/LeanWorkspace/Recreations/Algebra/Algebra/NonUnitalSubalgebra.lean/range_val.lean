import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

theorem range_val : NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S := NonUnitalSubalgebra.ext <| Set.ext_iff.1 <|
    (NonUnitalAlgHom.coe_range <| NonUnitalSubalgebraClass.subtype S).trans Subtype.range_val

