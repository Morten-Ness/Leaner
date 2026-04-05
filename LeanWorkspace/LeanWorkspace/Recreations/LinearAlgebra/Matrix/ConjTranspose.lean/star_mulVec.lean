import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable [NonUnitalSemiring α]

theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n → α) :
    star (M *ᵥ v) = star v ᵥ* Mᴴ := funext fun _ => (Matrix.star_dotProduct_star _ _).symm

