FAIL
import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_inj {n} {v w : Fin n → α} : Matrix.circulant v = Matrix.circulant w ↔ v = w := by
  constructor
  · intro h
    ext i
    cases n with
    | zero =>
        exact Fin.elim0 i
    | succ n =>
        let z : Fin (Nat.succ n) := 0
        have h' := congrArg (fun M => M z i) h
        simpa [Matrix.circulant_apply, z] using h'
  · intro h
    simp [h]
