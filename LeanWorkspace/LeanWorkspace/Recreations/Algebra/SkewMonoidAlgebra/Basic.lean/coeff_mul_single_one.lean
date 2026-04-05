import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Monoid G] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_mul_single_one (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (f * SkewMonoidAlgebra.single 1 r).coeff x = f.coeff x * x • r := SkewMonoidAlgebra.coeff_mul_single_aux f fun a ↦ by rw [mul_one]

