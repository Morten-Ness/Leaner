import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_fun_one : Function.mulSupport (fun _ ↦ 1 : ι → M) = ∅ := Function.mulSupport_one

