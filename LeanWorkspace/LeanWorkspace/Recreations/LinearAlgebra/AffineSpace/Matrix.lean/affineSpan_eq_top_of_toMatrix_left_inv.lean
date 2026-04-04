import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

theorem affineSpan_eq_top_of_toMatrix_left_inv [Finite ι] [Fintype ι'] [DecidableEq ι]
    [Nontrivial k] (p : ι' → P) {A : Matrix ι ι' k} (hA : A * b.toMatrix p = 1) :
    affineSpan k (Set.range p) = ⊤ := by
  cases nonempty_fintype ι
  suffices ∀ i, b i ∈ affineSpan k (Set.range p) by
    rw [eq_top_iff, ← b.tot, affineSpan_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  have hAi : ∑ j, A i j = 1 := by
    calc
      ∑ j, A i j = ∑ j, A i j * ∑ l, b.toMatrix p j l := by simp
      _ = ∑ j, ∑ l, A i j * b.toMatrix p j l := by simp_rw [Finset.mul_sum]
      _ = ∑ l, ∑ j, A i j * b.toMatrix p j l := by rw [Finset.sum_comm]
      _ = ∑ l, (A * b.toMatrix p) i l := rfl
      _ = 1 := by simp [hA, Matrix.one_apply]
  have hbi : b i = Finset.univ.affineCombination k p (A i) := by
    apply b.ext_elem
    intro j
    rw [b.coord_apply, Finset.univ.map_affineCombination _ _ hAi,
      Finset.univ.affineCombination_eq_linear_combination _ _ hAi]
    change _ = (A * b.toMatrix p) i j
    simp_rw [hA, Matrix.one_apply, @eq_comm _ i j]
  rw [hbi]
  exact affineCombination_mem_affineSpan hAi p

