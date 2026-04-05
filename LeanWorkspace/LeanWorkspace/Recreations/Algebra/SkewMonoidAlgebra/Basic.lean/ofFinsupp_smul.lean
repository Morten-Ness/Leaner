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

theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G →₀ k) :
    (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G) := show _ = smul _ _ by rw [smul]

