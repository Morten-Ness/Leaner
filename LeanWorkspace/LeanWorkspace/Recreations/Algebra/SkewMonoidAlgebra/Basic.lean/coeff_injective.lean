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

theorem coeff_injective : Function.Injective (SkewMonoidAlgebra.coeff : SkewMonoidAlgebra k G → G → k) := by
  rintro ⟨p⟩ ⟨q⟩
  simp only [SkewMonoidAlgebra.coeff, DFunLike.coe_fn_eq, imp_self, ofFinsupp.injEq]

