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

theorem coeff_mul_single (f : SkewMonoidAlgebra k G) (r : k) (x y : G) :
    (f * SkewMonoidAlgebra.single x r).coeff y = f.coeff (y * x⁻¹) * (y * x⁻¹) • r := SkewMonoidAlgebra.coeff_mul_single_aux f fun _a ↦ eq_mul_inv_iff_mul_eq.symm

