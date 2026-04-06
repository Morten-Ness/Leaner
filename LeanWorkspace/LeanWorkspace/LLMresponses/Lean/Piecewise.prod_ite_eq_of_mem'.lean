FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_eq_of_mem' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) (h : a ∈ s) :
    (∏ x ∈ s, if x = a then b x else 1) = b a := by
  classical
  rw [Finset.prod_biUnion]
  · rw [Finset.biUnion_insert]
    · simp [h]
    · simp
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_singleton]
    aesop
