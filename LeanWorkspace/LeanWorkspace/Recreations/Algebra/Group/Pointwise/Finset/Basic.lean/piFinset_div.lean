import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]
  [∀ i, DecidableEq (α i)]

theorem piFinset_div [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i / t i) = piFinset s / piFinset t := piFinset_image₂ _ _ _

