FAIL
import Mathlib

open scoped DirectSum

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem fromDirectSumEquiv_symm_apply [Finite ι] [(i : ι) → DecidableEq (κ i)]
    (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : (i : ι) → κ i) :
    MultilinearMap.fromDirectSumEquiv.symm f p = f.compLinearMap (fun i ↦ DirectSum.lof _ _ _ (p i)) := by
  ext x
  simp [MultilinearMap.fromDirectSumEquiv, MultilinearMap.compLinearMap]
