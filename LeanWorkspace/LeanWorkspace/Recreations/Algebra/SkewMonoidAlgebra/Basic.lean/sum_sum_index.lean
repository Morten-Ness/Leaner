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

theorem sum_sum_index {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    {f : SkewMonoidAlgebra M α} {g : α → M → SkewMonoidAlgebra N β} {h : β → N → P}
    (h_zero : ∀ (a : β), h a 0 = 0)
    (h_add : ∀ (a : β) (b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    SkewMonoidAlgebra.sum (SkewMonoidAlgebra.sum f g) h = SkewMonoidAlgebra.sum f fun a b ↦ SkewMonoidAlgebra.sum (g a b) h := by
  rw [SkewMonoidAlgebra.sum_def, SkewMonoidAlgebra.toFinsupp_sum' f g, Finsupp.sum_sum_index h_zero h_add]; simp [SkewMonoidAlgebra.sum_def]

