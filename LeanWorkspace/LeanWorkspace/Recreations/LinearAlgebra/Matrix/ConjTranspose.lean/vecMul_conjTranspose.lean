import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable [NonUnitalSemiring α]

theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n → α) :
    x ᵥ* Aᴴ = star (A *ᵥ star x) := funext fun _ => Matrix.dotProduct_star _ _

