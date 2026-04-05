import Mathlib

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}

variable [CommSemiring R]

variable [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

theorem directSum_ext [Finite ι] [(i : ι) → DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'⦄
    (h : ∀ p : (i : ι) → κ i,
      f.compLinearMap (fun i => DirectSum.lof _ _ _ (p i)) =
      g.compLinearMap (fun i => DirectSum.lof _ _ _ (p i))) : f = g := dfinsupp_ext h

