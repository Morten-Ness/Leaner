FAIL
import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_isSymm_apply {n} {v : Fin n → α} (h : (Matrix.circulant v).IsSymm) (i : Fin n) :
    v (-i) = v i := by
  rw [Matrix.IsSymm] at h
  have := congrArg (fun M => M i 0) h
  simpa [Matrix.circulant_apply] using this
