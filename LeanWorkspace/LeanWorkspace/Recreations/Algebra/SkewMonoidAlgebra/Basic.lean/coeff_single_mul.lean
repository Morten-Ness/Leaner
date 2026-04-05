import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Group G] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_single_mul (r : k) (x : G) (f : SkewMonoidAlgebra k G) (y : G) :
    (SkewMonoidAlgebra.single x r * f).coeff y = r * x • f.coeff (x⁻¹ * y) := SkewMonoidAlgebra.coeff_single_mul_aux f fun _z ↦ eq_inv_mul_iff_mul_eq.symm

