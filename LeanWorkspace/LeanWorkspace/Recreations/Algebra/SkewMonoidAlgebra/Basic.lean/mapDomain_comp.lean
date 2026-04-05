import Mathlib

variable {k G : Type*}

variable [AddCommMonoid k]

variable {G' G'' : Type*} (f : G → G') {g : G' → G''} (v : SkewMonoidAlgebra k G)

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem mapDomain_comp : SkewMonoidAlgebra.mapDomain (g ∘ f) v = SkewMonoidAlgebra.mapDomain g (SkewMonoidAlgebra.mapDomain f v) := ((SkewMonoidAlgebra.sum_sum_index (SkewMonoidAlgebra.single_zero <| g ·) (SkewMonoidAlgebra.single_add <| g ·)).trans
    (SkewMonoidAlgebra.sum_congr fun _ _ ↦ SkewMonoidAlgebra.sum_single_index (SkewMonoidAlgebra.single_zero _))).symm

