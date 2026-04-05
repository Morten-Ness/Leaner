import Mathlib

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

variable [DecidableEq ι]

theorem fromDirectSumEquiv_lof [Finite ι] [(i : ι) → DecidableEq (κ i)]
    (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (p : (i : ι) → κ i) (x : (i : ι) → M i (p i)) :
    MultilinearMap.fromDirectSumEquiv f (fun i => lof R _ _ _ (x i)) = f p x := by
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [MultilinearMap.fromDirectSumEquiv, ← fromDFinsuppEquiv_single]
  convert rfl

set_option backward.isDefEq.respectTransparency false in

