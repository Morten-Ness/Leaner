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

theorem sum_mapDomain_index {k' : Type*} [AddCommMonoid k'] {h : G' → k → k'}
    (h_zero : ∀ (b : G'), h b 0 = 0)
    (h_add : ∀ (b : G') (m₁ m₂ : k), h b (m₁ + m₂) = h b m₁ + h b m₂) :
    SkewMonoidAlgebra.sum (SkewMonoidAlgebra.mapDomain f v) h = SkewMonoidAlgebra.sum v fun a m ↦ h (f a) m := (SkewMonoidAlgebra.sum_sum_index h_zero h_add).trans <| SkewMonoidAlgebra.sum_congr fun _ _ ↦ SkewMonoidAlgebra.sum_single_index (h_zero _)

