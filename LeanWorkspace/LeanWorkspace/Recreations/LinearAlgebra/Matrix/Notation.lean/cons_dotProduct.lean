import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [AddCommMonoid α] [Mul α]

theorem cons_dotProduct (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

