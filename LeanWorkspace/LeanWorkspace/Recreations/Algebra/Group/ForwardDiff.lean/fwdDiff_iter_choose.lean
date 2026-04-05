import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_iter_choose (j k : ℕ) :
    Δ_[1]^[k] (fun x ↦ x.choose (k + j) : ℕ → ℤ) = fun x ↦ x.choose j := by
  induction k generalizing j with
  | zero => simp only [zero_add, iterate_zero, id_eq]
  | succ k IH =>
    simp only [iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]

