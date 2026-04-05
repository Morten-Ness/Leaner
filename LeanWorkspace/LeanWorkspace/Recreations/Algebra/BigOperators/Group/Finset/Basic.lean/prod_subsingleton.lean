import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_subsingleton [Subsingleton ι] (f : ι → M) (a : ι) : ∏ x : ι, f x = f a := by
  have : Unique ι := uniqueOfSubsingleton a
  rw [Fintype.prod_unique f, Subsingleton.elim default a]

