import Mathlib

variable {k G : Type*}

variable [AddMonoid k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem ext_iff {p q : SkewMonoidAlgebra k G} : p = q ↔ ∀ n, SkewMonoidAlgebra.coeff p n = SkewMonoidAlgebra.coeff q n := by
  rcases p with ⟨f : G →₀ k⟩
  rcases q with ⟨g : G →₀ k⟩
  simpa [SkewMonoidAlgebra.coeff] using DFunLike.ext_iff (f := f) (g := g)

