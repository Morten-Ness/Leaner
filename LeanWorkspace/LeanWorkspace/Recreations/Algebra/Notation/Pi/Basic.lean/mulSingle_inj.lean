import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_inj (i : ι) {x y : M i} : Pi.mulSingle i x = Pi.mulSingle i y ↔ x = y := (Pi.mulSingle_injective _).eq_iff

