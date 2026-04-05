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

theorem sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : s.sum f * b = s.sum fun a c ↦ f a c * b := by
  simp only [SkewMonoidAlgebra.sum, Finsupp.sum, Finset.sum_mul]

