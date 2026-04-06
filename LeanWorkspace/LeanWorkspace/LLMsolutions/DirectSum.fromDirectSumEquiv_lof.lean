import Mathlib

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem fromDirectSumEquiv_lof [Finite ι] [(i : ι) → DecidableEq (κ i)]
    (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (p : (i : ι) → κ i) (x : (i : ι) → M i (p i)) :
    MultilinearMap.fromDirectSumEquiv f (fun i => DirectSum.lof R _ _ _ (x i)) = f p x := by
  simpa using MultilinearMap.fromDirectSumEquiv_lof (R := R) (f := f) (p := p) (x := x)
