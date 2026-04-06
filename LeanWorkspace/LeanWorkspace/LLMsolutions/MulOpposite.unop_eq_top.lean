FAIL
import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_eq_top {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      have : MulOpposite.unop x ∈ S.unop := hx
      simpa [h] using this
  · intro h
    rw [h]
    rfl
