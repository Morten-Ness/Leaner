import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem Exact.hasZeroObject (h : S.Exact) : HasZeroObject C := ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

