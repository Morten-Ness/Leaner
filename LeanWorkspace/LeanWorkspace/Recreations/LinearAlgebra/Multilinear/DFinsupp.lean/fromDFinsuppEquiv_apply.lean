import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

theorem fromDFinsuppEquiv_apply
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (x : Π i, Π₀ (j : κ i), M i j) :
    MultilinearMap.fromDFinsuppEquiv κ R f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

