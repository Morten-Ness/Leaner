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

theorem induction_on {p : SkewMonoidAlgebra k G → Prop} (f : SkewMonoidAlgebra k G)
    (zero : p 0) (SkewMonoidAlgebra.single : ∀ g a, p (SkewMonoidAlgebra.single g a)) (add : ∀ f g :
    SkewMonoidAlgebra k G, p f → p g → p (f + g)) : p f := by
  rw [← SkewMonoidAlgebra.sum_single f, SkewMonoidAlgebra.sum_def']
  exact Finset.sum_induction _ _ add zero (by simp_all)

