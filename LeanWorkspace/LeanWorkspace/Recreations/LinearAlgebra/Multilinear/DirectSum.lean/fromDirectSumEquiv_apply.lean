import Mathlib

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

variable [DecidableEq ι]

open scoped DirectSum

set_option backward.isDefEq.respectTransparency false in
theorem fromDirectSumEquiv_apply [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : ⨁ i, ⨁ (j : κ i), M i j) :
    MultilinearMap.fromDirectSumEquiv f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  rw [MultilinearMap.fromDirectSumEquiv, ← MultilinearMap.fromDFinsuppEquiv_apply]
  convert rfl
