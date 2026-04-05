import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem ne_zero_of_mem_nthRootsFinset {η : R} {a : R} (ha : a ≠ 0) (hη : η ∈ Polynomial.nthRootsFinset n a) :
    η ≠ 0 := by
  rintro rfl
  cases n with
  | zero =>
    simp only [Polynomial.nthRootsFinset_zero, notMem_empty] at hη
  | succ n =>
    rw [Polynomial.mem_nthRootsFinset n.succ_pos, zero_pow n.succ_ne_zero] at hη
    exact ha hη.symm

