import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

theorem multiset_prod_X_sub_C_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => Polynomial.X - Polynomial.C x).prod = -t.sum := by
  rw [nextCoeff_multiset_prod]
  · simp only [nextCoeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply Polynomial.monic_X_sub_C

