import Mathlib

variable {ι ι' R : Type*} {κ : ι → Type*}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeFinsuppEquiv_single (p : ((Π i, κ i) × ι')) (r : R) (x : Π i, (κ i →₀ R)) :
    MultilinearMap.freeFinsuppEquiv (Finsupp.single p r) x = r • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  classical
  ext j y
  by_cases hj : j = p.2
  · subst hj
    simp [MultilinearMap.freeFinsuppEquiv, Finsupp.single_apply]
  · simp [MultilinearMap.freeFinsuppEquiv, Finsupp.single_apply, hj]
