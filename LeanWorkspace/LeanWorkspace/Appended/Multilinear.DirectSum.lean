import Mathlib

section

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

variable [DecidableEq ι]

theorem fromDirectSumEquiv_apply [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : (p : (i : ι) → κ i) → MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : ⨁ i, ⨁ (j : κ i), M i j) :
    MultilinearMap.fromDirectSumEquiv f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  rw [MultilinearMap.fromDirectSumEquiv, ← fromDFinsuppEquiv_apply]
  convert rfl

set_option backward.isDefEq.respectTransparency false in

end

section

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

end

section

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

end
