import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_singleton' (a : ι) :
    Finset.prod (singleton a) = fun (f : ι → M) => f a := by
  funext f
  simp

