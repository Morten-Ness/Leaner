import Mathlib

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

variable [DecidableEq ι]

theorem fromDirectSumEquiv_symm_apply [Finite ι] [(i : ι) → DecidableEq (κ i)]
    (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : (i : ι) → κ i) :
    MultilinearMap.fromDirectSumEquiv.symm f p = f.compLinearMap (fun i ↦ DirectSum.lof _ _ _ (p i)) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  simp_rw [MultilinearMap.fromDirectSumEquiv, DirectSum.lof, ← fromDFinsuppEquiv_symm_apply]
  convert rfl

