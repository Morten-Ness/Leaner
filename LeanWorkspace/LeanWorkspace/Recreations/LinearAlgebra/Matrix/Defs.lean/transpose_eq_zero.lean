import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0 := transpose_inj

