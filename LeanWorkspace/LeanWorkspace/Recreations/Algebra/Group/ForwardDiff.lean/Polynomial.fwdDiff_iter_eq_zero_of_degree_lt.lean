import Mathlib

open scoped Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

variable {R : Type*} [CommRing R]

theorem Polynomial.fwdDiff_iter_eq_zero_of_degree_lt {P : R[X]} {n : ℕ} (hP : P.natDegree < n) :
    Δ_[1]^[n] P.eval = 0 := funext fun x ↦ by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hP
  rw [add_assoc, add_comm, Function.iterate_add_apply, Function.iterate_succ_apply,
    P.fwdDiff_iter_degree_eq_factorial, Pi.smul_def]
  simp [fwdDiff_iter_eq_sum_shift]

