FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_eq_of_mem [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  classical
  have h1 :
      (∏ x in s, if a = x then b x else 1) =
        ∏ x in s, if x = a then b a else 1 := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      simp
    · simp [hxa, eq_comm]
  rw [h1]
  exact Finset.prod_ite_eq_of_mem h b
