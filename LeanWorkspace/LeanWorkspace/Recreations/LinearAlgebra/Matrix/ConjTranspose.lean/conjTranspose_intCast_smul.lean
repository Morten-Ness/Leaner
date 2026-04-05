import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : ℤ)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ := Matrix.ext <| by simp

