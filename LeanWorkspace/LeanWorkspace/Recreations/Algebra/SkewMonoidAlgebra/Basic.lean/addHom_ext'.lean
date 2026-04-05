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

theorem addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g : SkewMonoidAlgebra k G →+ N⦄
    (H : ∀ x, f.comp (SkewMonoidAlgebra.singleAddHom x) = g.comp (SkewMonoidAlgebra.singleAddHom x)) : f = g := SkewMonoidAlgebra.addHom_ext fun x ↦ DFunLike.congr_fun (H x)

