import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_eq_top {S : Submonoid M} : S.op = ⊤ ↔ S = ⊤ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      trivial
    · intro _
      have hop : MulOpposite.op x ∈ S.op := by
        simpa [h]
      simpa using hop
  · intro h
    ext x
    constructor
    · intro hx
      trivial
    · intro _
      have hS : S = ⊤ := h
      simpa [hS] using (show MulOpposite.unop x ∈ S from trivial)
