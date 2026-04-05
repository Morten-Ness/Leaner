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

theorem sum_smul_index' {N R : Type*} [AddCommMonoid k]
    [DistribSMul R k] [AddCommMonoid N]
    {g : SkewMonoidAlgebra k G} {b : R} {h : G → k → N} (h0 : ∀ i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b • ·) := by
  simp only [SkewMonoidAlgebra.sum_def, SkewMonoidAlgebra.toFinsupp_smul, Finsupp.sum_smul_index' h0]

