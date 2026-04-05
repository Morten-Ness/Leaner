import Mathlib

variable {k G : Type*}

variable [AddCommMonoid k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem ofFinsupp_sum {k' G' : Type*} [AddCommMonoid k'] (f : G →₀ k)
    (g : G → k → G' →₀ k') :
    (⟨Finsupp.sum f g⟩ : SkewMonoidAlgebra k' G') = SkewMonoidAlgebra.sum ⟨f⟩ (⟨g · ·⟩) := by
  apply SkewMonoidAlgebra.toFinsupp_injective; simp only [SkewMonoidAlgebra.toFinsupp_sum']

