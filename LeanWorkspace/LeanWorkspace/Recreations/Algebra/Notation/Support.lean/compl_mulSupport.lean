import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem compl_mulSupport : (Function.mulSupport f)ᶜ = {x | f x = 1} := ext fun _ ↦ Function.notMem_mulSupport

