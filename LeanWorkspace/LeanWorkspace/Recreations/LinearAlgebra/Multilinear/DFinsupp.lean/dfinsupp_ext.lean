import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : Type uN}

variable [Finite ι] [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [AddCommMonoid N]

variable [∀ i k, Module R (M i k)] [Module R N]

theorem dfinsupp_ext [∀ i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => DFinsupp.lsingle (p i)) =
      g.compLinearMap (fun i => DFinsupp.lsingle (p i))) : f = g := by
  ext x
  change f (fun i ↦ x i) = g (fun i ↦ x i)
  classical
  cases nonempty_fintype ι
  rw [funext (fun i ↦ Eq.symm (DFinsupp.sum_single (f := x i)))]
  simp_rw [DFinsupp.sum, MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

