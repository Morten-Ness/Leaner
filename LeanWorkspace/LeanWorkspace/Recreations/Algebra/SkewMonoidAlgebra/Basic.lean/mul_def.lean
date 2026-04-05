import Mathlib

variable {k G : Type*}

variable [Mul G]

variable [SMul G k] [NonUnitalNonAssocSemiring k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem mul_def {f g : SkewMonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦ SkewMonoidAlgebra.single (a₁ * a₂) (b₁ * (a₁ • b₂)) := rfl

