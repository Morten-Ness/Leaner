import Mathlib

variable {R : Type*} [CommRing R]

theorem Ideal.Quotient.index_eq_zero (I : Ideal R) : (↑I.toAddSubgroup.index : R ⧸ I) = 0 := by
  rw [AddSubgroup.index, Nat.card_eq]
  split_ifs with hq; swap
  · simp
  letI : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)

