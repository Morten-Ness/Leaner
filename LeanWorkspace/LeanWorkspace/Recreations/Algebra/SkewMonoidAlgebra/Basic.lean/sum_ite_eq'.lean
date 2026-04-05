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

set_option backward.isDefEq.respectTransparency false in
theorem sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
    (a : G) (b : G → k → N) : (f.sum fun (x : G) (v : k) ↦ if x = a then b x v else 0) =
      if a ∈ f.support then b a (f.coeff a) else 0 := by
  simp only [SkewMonoidAlgebra.sum_def', f.toFinsupp.support.sum_ite_eq', SkewMonoidAlgebra.support]

