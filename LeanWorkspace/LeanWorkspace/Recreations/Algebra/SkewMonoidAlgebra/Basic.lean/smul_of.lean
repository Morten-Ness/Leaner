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

theorem smul_of (g : G) (r : k) : r • SkewMonoidAlgebra.of k G g = SkewMonoidAlgebra.single g r := by
  rw [SkewMonoidAlgebra.of_apply, SkewMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

