import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]

theorem piFinset_smul [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ s i • t i) = piFinset s • piFinset t := piFinset_image₂ _ _ _

