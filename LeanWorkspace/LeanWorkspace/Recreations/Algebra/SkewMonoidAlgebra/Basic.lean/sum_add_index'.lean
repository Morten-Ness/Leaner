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

theorem sum_add_index' {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G → k → S}
    (hf : ∀ i, h i 0 = 0) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.toFinsupp + g.toFinsupp⟩ by rw [SkewMonoidAlgebra.ofFinsupp_add, SkewMonoidAlgebra.eta]]
  exact Finsupp.sum_add_index' hf h_add

