import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem rootMultiplicity_eq_multiplicity [DecidableEq R]
    (p : R[X]) (a : R) :
    Polynomial.rootMultiplicity a p =
      if p = 0 then 0 else multiplicity (Polynomial.X - Polynomial.C a) p := by
  simp only [Polynomial.rootMultiplicity, multiplicity, emultiplicity]
  split
  · rfl
  rename_i h
  simp only [Polynomial.finiteMultiplicity_X_sub_C a h, ↓reduceDIte]
  rw [← ENat.some_eq_coe, WithTop.untopD_coe]
  congr

