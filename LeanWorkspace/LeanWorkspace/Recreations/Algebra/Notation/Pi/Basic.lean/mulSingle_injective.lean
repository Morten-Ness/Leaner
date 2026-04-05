import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_injective (i : ι) : Function.Injective (Pi.mulSingle i : M i → ∀ i, M i) := Function.update_injective _ i

