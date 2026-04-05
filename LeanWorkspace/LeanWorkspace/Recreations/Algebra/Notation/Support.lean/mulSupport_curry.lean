import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_curry (f : ι × κ → M) : (Function.mulSupport f.curry) = (Function.mulSupport f).image Prod.fst := by
  simp [Function.mulSupport, funext_iff, image]

