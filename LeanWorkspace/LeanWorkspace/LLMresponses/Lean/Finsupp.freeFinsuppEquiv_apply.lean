import Mathlib

variable {ι ι' R : Type*} {κ : ι → Type*}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeFinsuppEquiv_apply [Fintype ι']
  (f : ((Π i, κ i) × ι') →₀ R) (x : Π i, (κ i →₀ R)) :
  MultilinearMap.freeFinsuppEquiv f x = ∑ p, f p • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  ext j
  simp [MultilinearMap.freeFinsuppEquiv_apply]
