import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

theorem leadingCoeff_multiset_prod :
    t.prod.leadingCoeff = (t.map fun f => leadingCoeff f).prod := by
  rw [← leadingCoeffHom_apply, MonoidHom.map_multiset_prod]
  simp only [leadingCoeffHom_apply]

