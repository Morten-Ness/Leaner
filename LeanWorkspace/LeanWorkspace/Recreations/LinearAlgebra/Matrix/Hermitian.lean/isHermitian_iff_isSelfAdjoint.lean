import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem isHermitian_iff_isSelfAdjoint {A : Matrix n n α} :
    A.IsHermitian ↔ IsSelfAdjoint A := Iff.rfl

protected alias ⟨Matrix.IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=
  isHermitian_iff_isSelfAdjoint

