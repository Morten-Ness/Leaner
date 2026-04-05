import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {M N : Matrix m n α}

theorem ext : (∀ i j, M i j = N i j) → M = N := Matrix.ext_iff.mp

