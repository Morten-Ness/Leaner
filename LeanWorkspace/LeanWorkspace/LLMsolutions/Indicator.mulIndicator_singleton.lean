import Mathlib

variable {α β M N : Type*}

variable {ι : Type*} [DecidableEq ι] {M : Type*} [One M]

theorem mulIndicator_singleton (i : ι) (f : ι → M) :
    Set.mulIndicator {i} f = Pi.mulSingle i (f i) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [Set.mulIndicator, Pi.mulSingle]
  · simp [Set.mulIndicator, Pi.mulSingle, h]
