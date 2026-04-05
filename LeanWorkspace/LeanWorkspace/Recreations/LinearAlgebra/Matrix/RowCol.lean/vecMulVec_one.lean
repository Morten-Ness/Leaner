import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem vecMulVec_one [MulOneClass R] (x : n → R) :
    vecMulVec x 1 = Matrix.replicateCol m x := by
  ext; simp [vecMulVec_apply]

