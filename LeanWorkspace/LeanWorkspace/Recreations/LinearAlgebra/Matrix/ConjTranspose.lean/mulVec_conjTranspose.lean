import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable [NonUnitalSemiring α]

theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m → α) :
    Aᴴ *ᵥ x = star (star x ᵥ* A) := funext fun _ => Matrix.star_dotProduct _ _

