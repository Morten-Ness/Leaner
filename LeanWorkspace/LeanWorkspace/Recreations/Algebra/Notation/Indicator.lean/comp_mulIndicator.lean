import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem comp_mulIndicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  letI := Classical.decPred (· ∈ s)
  convert s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2

