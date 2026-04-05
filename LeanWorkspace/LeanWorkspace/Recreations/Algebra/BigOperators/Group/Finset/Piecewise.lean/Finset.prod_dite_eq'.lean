import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ∀ x : ι, x = a → M) :
    ∏ x ∈ s, (if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

