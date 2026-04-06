FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι → M}

theorem prod_sdiff_ne_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i ≠ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≠ ∏ i ∈ t, f i := by
  classical
  rw [← Finset.prod_sdiff (by exact Finset.inter_subset_left : s ∩ t ⊆ s)]
  rw [← Finset.prod_sdiff (by exact Finset.inter_subset_right : s ∩ t ⊆ t)]
  constructor
  · intro h hs
    apply h
    exact mul_right_cancelₓ hs
  · intro h hsd
    apply h
    exact congrArg (fun x => x * ∏ i ∈ s ∩ t, f i) hsd
