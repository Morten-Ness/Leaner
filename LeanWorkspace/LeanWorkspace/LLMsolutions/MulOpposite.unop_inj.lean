import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := by
  constructor
  · intro h
    ext x
    change MulOpposite.unop x ∈ S.unop ↔ MulOpposite.unop x ∈ T.unop
    simpa [h]
  · intro h
    simp [h]
