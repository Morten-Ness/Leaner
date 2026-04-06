FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_subsingleton [Subsingleton ι] (f : ι → M) (a : ι) : ∏ x : ι, f x = f a := by
  classical
  have h : (univ : Finset ι) = {a} := by
    ext x
    simp [Subsingleton.elim x a]
  simp [Fintype.prod_of_finset, h]
