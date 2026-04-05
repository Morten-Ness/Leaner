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

theorem eq_liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R) (g : G → R)
    (l : SkewMonoidAlgebra k G →+ R) (h : ∀ a b, l (SkewMonoidAlgebra.single a b) = f b * g a) : l = SkewMonoidAlgebra.liftNC f g := by
  ext a b; simp_all

