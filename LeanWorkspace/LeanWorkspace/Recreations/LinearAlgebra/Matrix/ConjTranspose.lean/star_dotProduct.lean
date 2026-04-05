import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable [Fintype m] [Fintype n]

variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dotProduct]

