import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Monoid G] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem ringHom_ext' {f g : SkewMonoidAlgebra k G →+* k}
    (h₁ : f.comp SkewMonoidAlgebra.singleOneRingHom = g.comp SkewMonoidAlgebra.singleOneRingHom)
    (h_of : (f : SkewMonoidAlgebra k G →* k).comp (SkewMonoidAlgebra.of k G) =
      (g : SkewMonoidAlgebra k G →* k).comp (SkewMonoidAlgebra.of k G)) : f = g := SkewMonoidAlgebra.ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

