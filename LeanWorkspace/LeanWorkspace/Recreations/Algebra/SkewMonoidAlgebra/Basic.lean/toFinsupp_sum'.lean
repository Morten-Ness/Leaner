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

theorem toFinsupp_sum' {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G)
    (g : G → k → SkewMonoidAlgebra k' G') :
    (SkewMonoidAlgebra.sum f g).toFinsupp = Finsupp.sum f.toFinsupp (toFinsupp <| g · ·) := SkewMonoidAlgebra.map_sum _root_ SkewMonoidAlgebra.toFinsuppAddEquiv (fun a ↦ g a (f.coeff a)) f.toFinsupp.support

