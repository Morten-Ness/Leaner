FAIL
import Mathlib

variable {R A : Type*}

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

theorem charZero_of_isFractionRing [CharZero R] : CharZero K := by
  classical
  refine ⟨?_⟩
  intro m n hmn
  by_contra hne
  wlog hlt : m < n := lt_of_le_of_ne (Nat.le_total m n).resolve_right (Ne.symm hne)
  · exact this n m (by simpa [eq_comm] using hmn.symm) (Ne.symm hne) ((Nat.lt_total m n).resolve_left hlt)
  have hsub : (n - m : R) = 0 := by
    apply (Nat.cast_injective (R := R))
    simpa [Nat.cast_sub hlt.le] using congrArg (fun x : K => x - m) hmn
  have : (n - m : ℕ) = 0 := Nat.cast_injective (R := R) hsub
  have : n - m = 0 := this
  exact hlt.ne' (Nat.sub_eq_zero_iff_le.mp this)
