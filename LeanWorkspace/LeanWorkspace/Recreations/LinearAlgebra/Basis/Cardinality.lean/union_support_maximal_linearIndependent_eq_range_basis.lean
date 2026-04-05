import Mathlib

variable {R : Type u} {M : Type v}

variable [Semiring R] [AddCommMonoid M] [Nontrivial R] [Module R M]

theorem union_support_maximal_linearIndependent_eq_range_basis {ι : Type w} (b : Basis ι R M)
    {κ : Type w'} (v : κ → M) (ind : LinearIndependent R v) (m : ind.Maximal) :
    ⋃ k, ((b.repr (v k)).support : Set ι) = Set.univ := by
  -- If that's not the case,
  by_contra h
  simp only [← Ne.eq_def, ne_univ_iff_exists_notMem, mem_iUnion, not_exists_not,
    Finsupp.mem_support_iff, Finset.mem_coe] at h
  -- We have some basis element `b i` which is not in the support of any of the `v k`.
  obtain ⟨i, w⟩ := h
  have repr_eq_zero (l) : b.repr (linearCombination R v l) i = 0 := by
    simp [linearCombination_apply, Finsupp.sum, w]
  -- Using this, we'll construct a linearly independent family strictly larger than `v`,
  -- by also using this `b i`.
  let v' (o : Option κ) : M := o.elim (b i) v
  have r : Set.range v ⊆ Set.range v' := by rintro - ⟨k, rfl⟩; exact ⟨some k, rfl⟩
  have r' : b i ∉ Set.range v := fun ⟨k, p⟩ ↦ by simpa [w] using congr(b.repr $p i)
  have r'' : Set.range v ≠ Set.range v' := (r' <| · ▸ ⟨none, rfl⟩)
  -- The key step in the proof is checking that this strictly larger family is linearly independent.
  have i' : LinearIndepOn R id (Set.range v') := by
    apply LinearIndependent.linearIndepOn_id
    rw [linearIndependent_iffₛ]
    intro l l' z
    simp_rw [linearCombination_option, v', Option.elim] at z
    change _ + linearCombination R v l.some = _ + linearCombination R v l'.some at z
    -- We have some equality between linear combinations of `b i` and the `v k`,
    -- and want to show the coefficients are equal.
    ext (_ | a)
    -- We'll first show the coefficient of `b i` is zero,
    -- by expressing the `v k` in the basis `b`, and using that the `v k` have no `b i` term.
    · simpa [repr_eq_zero] using congr(b.repr $z i)
    -- All the other coefficients are also equal, because `v` is linear independent,
    -- by comparing the coefficients in the basis `b`.
    have l₁ : l.some = l'.some := ind <| b.repr.injective <| ext fun j ↦ by
      obtain rfl | ne := eq_or_ne i j
      · simp_rw [repr_eq_zero]
      classical simpa [single_apply, ne] using congr(b.repr $z j)
    exact DFunLike.congr_fun l₁ a
  exact r'' (m (Set.range v') i' r)

