import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_prodMk' (f : ι → M × N) :
    Function.mulSupport f = (Function.mulSupport fun x ↦ (f x).1) ∪ Function.mulSupport fun x ↦ (f x).2 := by
  simp only [← Function.mulSupport_prodMk]

