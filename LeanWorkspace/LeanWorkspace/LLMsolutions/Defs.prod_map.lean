import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ → M) :
    ∏ x ∈ s.map e, f x = ∏ x ∈ s, f (e x) := by
  classical
  refine Finset.induction_on s ?h ?step
  · simp
  · intro a s ha hs
    simp [ha, hs]
