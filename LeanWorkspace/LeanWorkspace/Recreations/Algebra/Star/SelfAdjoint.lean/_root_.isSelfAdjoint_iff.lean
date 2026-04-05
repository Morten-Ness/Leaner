import Mathlib

variable {R A : Type*}

theorem _root_.isSelfAdjoint_iff [Star R] {x : R} : IsSelfAdjoint x ↔ star x = x := Iff.rfl

