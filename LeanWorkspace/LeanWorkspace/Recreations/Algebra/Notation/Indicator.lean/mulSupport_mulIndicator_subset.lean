import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) ⊆ s := fun _ hx =>
  hx.imp_symm fun h => Set.mulIndicator_of_notMem h f

