import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (w : m → α) (v : n → α) :
    vecMulVec w v = Matrix.replicateCol ι w * Matrix.replicateRow ι v := by
  ext
  simp [vecMulVec, mul_apply]

