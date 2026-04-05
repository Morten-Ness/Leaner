import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

theorem fromDFinsuppEquiv_single
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    MultilinearMap.fromDFinsuppEquiv κ R f (fun i => DFinsupp.single (p i) (x i)) = f p x := by
  simp [MultilinearMap.fromDFinsuppEquiv]

