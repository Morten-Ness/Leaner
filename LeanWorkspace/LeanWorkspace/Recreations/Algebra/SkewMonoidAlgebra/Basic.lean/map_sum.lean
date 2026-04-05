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

theorem map_sum {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [FunLike H N P]
    [AddMonoidHomClass H N P] (h : H) (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    h (SkewMonoidAlgebra.sum f g) = SkewMonoidAlgebra.sum f fun a b ↦ h (g a b) := _root_.map_sum h _ _

