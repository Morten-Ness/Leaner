import Mathlib

variable {k G : Type*}

variable [AddMonoid k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem single_add (a : G) (b₁ b₂ : k) : SkewMonoidAlgebra.single a (b₁ + b₂) = SkewMonoidAlgebra.single a b₁ + SkewMonoidAlgebra.single a b₂ := by
  simp [← SkewMonoidAlgebra.toFinsupp_inj]

