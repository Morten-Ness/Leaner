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

theorem single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} :
    (SkewMonoidAlgebra.single a₁ b₁) * (SkewMonoidAlgebra.single a₂ b₂) = SkewMonoidAlgebra.single (a₁ * a₂) (b₁ * a₁ • b₂) := (SkewMonoidAlgebra.sum_single_index (by simp [zero_mul, SkewMonoidAlgebra.single_zero, SkewMonoidAlgebra.sum_zero])).trans
    (SkewMonoidAlgebra.sum_single_index (by simp [smul_zero, mul_zero, SkewMonoidAlgebra.single_zero]))

