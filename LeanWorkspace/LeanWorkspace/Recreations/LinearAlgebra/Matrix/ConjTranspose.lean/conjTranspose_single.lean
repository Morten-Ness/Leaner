import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_single [DecidableEq n] [DecidableEq m] [AddMonoid α]
    [StarAddMonoid α] (i : m) (j : n) (a : α) :
    (single i j a)ᴴ = single j i (star a) := by
  change (single i j a).transpose.map starAddEquiv = single j i (star a)
  simp

