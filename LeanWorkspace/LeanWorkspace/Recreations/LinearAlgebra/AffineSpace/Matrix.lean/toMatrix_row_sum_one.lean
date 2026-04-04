import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

theorem toMatrix_row_sum_one [Fintype ι] (q : ι' → P) (i : ι') : ∑ j, b.toMatrix q i j = 1 := by
  simp

