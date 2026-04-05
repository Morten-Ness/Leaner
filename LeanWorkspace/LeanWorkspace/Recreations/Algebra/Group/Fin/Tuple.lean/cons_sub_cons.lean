import Mathlib

variable {α M : Type*} {n : ℕ}

variable [Sub α]

theorem cons_sub_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v - vecCons y w = vecCons (x - y) (v - w) := by simp

