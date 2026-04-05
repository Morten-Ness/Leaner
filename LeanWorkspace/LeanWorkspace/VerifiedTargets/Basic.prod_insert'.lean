import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_insert' [DecidableEq ι] (h : a ∉ s) :
    Finset.prod (insert a s) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_insert h]

