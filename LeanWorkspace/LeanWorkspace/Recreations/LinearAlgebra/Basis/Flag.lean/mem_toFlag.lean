import Mathlib

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem mem_toFlag (b : Module.Basis (Fin n) K V) {p : Submodule K V} : p ∈ b.toFlag ↔ ∃ k, b.flag k = p := Iff.rfl

