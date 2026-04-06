FAIL
import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  letI : Subsingleton R := h
  have h01 : (0 : R) = 1 := Subsingleton.elim _ _
  have hcast1 : ((1 : ℕ) : R) = 0 := by
    rw [Nat.cast_one, ← h01]
  have : 1 = v := (CharP.cast_eq_zero_iff (R := R) v 1).mp hcast1
  exact hv this.symm
