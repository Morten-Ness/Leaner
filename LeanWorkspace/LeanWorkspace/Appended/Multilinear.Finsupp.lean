import Mathlib

section

variable {ι ι' R : Type*} {κ : ι → Type*}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeFinsuppEquiv_apply [Fintype ι']
  (f : ((Π i, κ i) × ι') →₀ R) (x : Π i, (κ i →₀ R)) :
  MultilinearMap.freeFinsuppEquiv f x = ∑ p, f p • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | single p r => simp [Finsupp.single_apply]

end

section

variable {ι ι' R : Type*} {κ : ι → Type*}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeFinsuppEquiv_single (p : ((Π i, κ i) × ι')) (r : R) (x : Π i, (κ i →₀ R)) :
    MultilinearMap.freeFinsuppEquiv (Finsupp.single p r) x = r • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  simp [MultilinearMap.freeFinsuppEquiv_def]

end
