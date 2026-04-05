import Mathlib

variable {k G : Type*}

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem sum_smul_index {N : Type*} [AddCommMonoid N] [NonUnitalNonAssocSemiring k]
    {g : SkewMonoidAlgebra k G} {b : k} {h : G → k → N} (h0 : ∀ i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b * ·) := by
  simp [SkewMonoidAlgebra.sum_def, Finsupp.sum_smul_index' h0]

