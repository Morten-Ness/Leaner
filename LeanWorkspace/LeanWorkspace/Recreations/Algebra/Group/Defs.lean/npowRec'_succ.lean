import Mathlib

variable {G : Type*}

theorem npowRec'_succ {M : Type*} [Mul M] [One M] {k : ℕ} (_ : k ≠ 0) (m : M) :
    npowRec' (k + 1) m = npowRec' k m * m := match k with
  | _ + 1 => rfl

