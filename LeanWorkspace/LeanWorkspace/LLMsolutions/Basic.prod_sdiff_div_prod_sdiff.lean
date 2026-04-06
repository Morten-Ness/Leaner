FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  classical
  simp_rw [div_eq_mul_inv, Finset.prod_sdiff ?_, Finset.inter_eq_right.2]
  · rw [Finset.inter_comm]
  · exact fun x hx => by simp at hx
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_left
