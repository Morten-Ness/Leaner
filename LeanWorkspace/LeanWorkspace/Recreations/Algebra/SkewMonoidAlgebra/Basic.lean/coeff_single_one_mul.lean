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

theorem coeff_single_one_mul (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (SkewMonoidAlgebra.single (1 : G) r * f).coeff x = r * f.coeff x := by
  simp [SkewMonoidAlgebra.coeff_single_mul_aux, one_smul]

