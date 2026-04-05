import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {M : I → Type*}

variable [∀ i, CommMonoid (M i)]

theorem Finset.univ_prod_mulSingle [Fintype I] (f : ∀ i, M i) :
    (∏ i, Pi.mulSingle i (f i)) = f := by
  ext a
  simp

