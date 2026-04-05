import Mathlib

section

variable {α β M N : Type*}

variable {ι : Type*} [DecidableEq ι] {M : Type*} [One M]

theorem mulIndicator_singleton (i : ι) (f : ι → M) :
    Set.mulIndicator {i} f = Pi.mulSingle i (f i) := by
  ext j
  simp only [Set.mulIndicator_apply, Pi.mulSingle_apply, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h]

end
