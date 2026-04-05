import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : Type uN}

variable [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [AddCommMonoid N]

variable [∀ i k, Module R (M i k)] [Module R N]

theorem pi_ext [Finite ι] [∀ i, Finite (κ i)] [∀ i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ Π j : κ i, M i j) N⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => LinearMap.single R _ (p i)) =
      g.compLinearMap (fun i => LinearMap.single R _ (p i))) : f = g := by
  ext x
  change f (fun i ↦ x i) = g (fun i ↦ x i)
  obtain ⟨i⟩ := nonempty_fintype ι
  have (i : _) := (nonempty_fintype (κ i)).some
  have := Classical.decEq ι
  rw [funext (fun i ↦ Eq.symm (Finset.univ_sum_single (x i)))]
  simp_rw [MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

