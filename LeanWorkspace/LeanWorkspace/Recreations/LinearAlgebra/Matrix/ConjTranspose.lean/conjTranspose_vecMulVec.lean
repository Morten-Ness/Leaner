import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_vecMulVec [Mul α] [StarMul α] (w : m → α) (v : n → α) :
    (vecMulVec w v)ᴴ = vecMulVec (star v) (star w) := ext fun _ _ => star_mul _ _

