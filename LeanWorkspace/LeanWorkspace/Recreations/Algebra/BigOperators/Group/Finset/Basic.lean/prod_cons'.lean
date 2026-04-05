import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_cons' (h : a ∉ s) :
    Finset.prod (cons a s h) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_cons h]

