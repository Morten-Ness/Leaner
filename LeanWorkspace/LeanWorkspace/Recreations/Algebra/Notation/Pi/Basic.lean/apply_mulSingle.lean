import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem apply_mulSingle (f' : ∀ i, M i → N i) (hf' : ∀ i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) :
    f' j (Pi.mulSingle i x j) = Pi.mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', Pi.mulSingle] using Function.apply_update f' 1 i x j

