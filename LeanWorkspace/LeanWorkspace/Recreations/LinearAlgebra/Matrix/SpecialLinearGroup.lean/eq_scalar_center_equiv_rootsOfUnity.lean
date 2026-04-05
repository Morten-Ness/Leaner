import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem eq_scalar_center_equiv_rootsOfUnity
    (A : center (Matrix.SpecialLinearGroup n R)) :
    A = scalar n ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity A : Rˣ) : R) := by
  unfold Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity Or.by_cases
  split_ifs with h
  · subsingleton
  dsimp only
  generalize_proofs _ eq
  generalize max (Fintype.card n) 1 = c at eq
  subst eq
  rw [center_equiv_rootsOfUnity'_apply, rootsOfUnity.val_mkOfPowEq_coe,
    Matrix.SpecialLinearGroup.scalar_eq_coe_self_center]

