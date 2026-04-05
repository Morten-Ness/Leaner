import Mathlib

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

variable {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

variable [Fintype ι] [∀ i, Finite (κ i)]

theorem multilinearMap_apply_apply (ii : (Π i, κ i) × ι') (v) :
    Basis.multilinearMap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2 := by
  simp [Basis.multilinearMap_apply]

