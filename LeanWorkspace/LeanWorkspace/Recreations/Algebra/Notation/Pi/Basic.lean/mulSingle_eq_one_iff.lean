import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem mulSingle_eq_one_iff : Pi.mulSingle i x = 1 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ Pi.mulSingle_one i⟩
  rw [← Pi.mulSingle_eq_same i x, h, one_apply]

