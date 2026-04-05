import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable [NonUnitalSemiring α]

theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m → α) :
    star (v ᵥ* M) = Mᴴ *ᵥ star v := funext fun _ => (Matrix.star_dotProduct_star _ _).symm

