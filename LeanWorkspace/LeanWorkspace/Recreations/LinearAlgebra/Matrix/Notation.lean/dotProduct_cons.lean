import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [AddCommMonoid α] [Mul α]

theorem dotProduct_cons (v : Fin n.succ → α) (x : α) (w : Fin n → α) :
    v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

