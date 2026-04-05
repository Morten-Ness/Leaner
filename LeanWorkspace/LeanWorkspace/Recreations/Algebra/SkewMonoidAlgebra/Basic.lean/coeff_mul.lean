import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Mul G] [SMulZeroClass G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_mul [DecidableEq G] (f g : SkewMonoidAlgebra k G)
    (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦
      if a₁ * a₂ = x then b₁ * a₁ • b₂ else 0 := by
  rw [SkewMonoidAlgebra.mul_def, SkewMonoidAlgebra.coeff_sum]; congr; SkewMonoidAlgebra.ext
  rw [SkewMonoidAlgebra.coeff_sum]; congr; SkewMonoidAlgebra.ext
  exact SkewMonoidAlgebra.coeff_single_apply

