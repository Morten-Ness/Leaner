import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem one_vecMulVec [MulOneClass R] (x : n → R) :
    vecMulVec 1 x = Matrix.replicateRow m x := by
  ext; simp [vecMulVec_apply]

