import Mathlib

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

theorem apply_mulSingle₂ (f' : ∀ i, M i → N i → O i) (hf' : ∀ i, f' i 1 1 = 1) (i : ι)
    (x : M i) (y : N i) (j : ι) :
    f' j (Pi.mulSingle i x j) (Pi.mulSingle i y j) = Pi.mulSingle i (f' i x y) j := by
  by_cases h : j = i
  · subst h
    simp only [Pi.mulSingle_eq_same]
  · simp only [Pi.mulSingle_eq_of_ne h, hf']

