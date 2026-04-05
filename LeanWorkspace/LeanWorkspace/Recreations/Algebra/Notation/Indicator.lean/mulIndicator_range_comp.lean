import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_range_comp {ι : Sort*} (f : ι → α) (g : α → M) :
    Set.mulIndicator (range f) g ∘ f = g ∘ f := letI := Classical.decPred (· ∈ range f)
  piecewise_range_comp _ _ _

