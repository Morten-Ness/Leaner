import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable [SMulCommClass R B B] [IsScalarTower R B B]

theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = LinearMap.mul R A := rfl

