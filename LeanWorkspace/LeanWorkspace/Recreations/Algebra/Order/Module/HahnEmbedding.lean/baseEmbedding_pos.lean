import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem baseEmbedding_pos {x : seed.baseEmbedding.domain} (hx : 0 < x) :
    0 < seed.baseEmbedding x := by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [HahnEmbedding.Seed.domain_baseEmbedding seed] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x ↦ x.val) := by
    rw [hf]
    simpa using hx
  have hsupport : f.support.Nonempty := by
    obtain hne := hfpos.ne.symm
    contrapose! hne with hempty
    apply DFinsupp.sum_eq_zero
    intro c
    simpa using DFinsupp.notMem_support_iff.mp (Finset.eq_empty_iff_forall_notMem.mp hempty c)
  -- The dictating term for `HahnSeries` < is at the lowest archimedean class of `f.support`
  refine (HahnSeries.lt_iff _ _).mpr ⟨f.support.min' hsupport, ?_, ?_⟩
  · intro j hj
    rw [HahnEmbedding.Seed.coeff_baseEmbedding seed hf.symm]
    rw [DFinsupp.notMem_support_iff.mp ?_]
    · simp
    contrapose! hj
    rw [← Subtype.coe_le_coe, Subtype.coe_mk]
    exact Finset.min'_le f.support _ hj
  -- Show that `f`'s value at dominating archimedean class is positive
  rw [HahnEmbedding.Seed.coeff_baseEmbedding seed hf.symm]
  suffices (seed.coeff (f.support.min' hsupport)) 0 <
      (seed.coeff (f.support.min' hsupport)) (f (f.support.min' hsupport)) by
    simpa using this
  suffices 0 < (f (f.support.min' hsupport)).val by
    apply (seed.strictMono_coeff (f.support.min' hsupport))
    simpa using this
  -- using the fact that `f.sum` is positive, we only needs to show that
  -- the remaining terms of f after removing the dominating class is of higher class
  apply ArchimedeanClass.pos_of_pos_of_mk_lt hfpos
  rw [ArchimedeanClass.mk_sub_comm]
  have hferase : (f.sum fun _ x ↦ x.val) - (f (f.support.min' hsupport)).val =
      ∑ x ∈ f.support.erase (f.support.min' hsupport), (f x).val :=
    sub_eq_of_eq_add (Finset.sum_erase_add _ _ (Finset.min'_mem _ hsupport)).symm
  rw [hferase]
  -- Now both sides are `HahnEmbedding.Seed.mk (∑ ...)`
  -- We rewrite them to `HahnEmbedding.Seed.mk (dominating term)`
  have hmono : StrictMonoOn (fun x ↦ ArchimedeanClass.mk (f x).val) f.support := by
    intro c hc d hd h
    simp only
    rw [HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum seed (f c).prop (by simpa using hc)]
    rw [HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum seed (f d).prop (by simpa using hd)]
    exact h
  rw [DFinsupp.sum, ArchimedeanClass.mk_sum hsupport hmono]
  rw [HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum seed (f _).prop
    (by simpa using f.support.min'_mem hsupport)]
  by_cases! hsupport' : (f.support.erase (f.support.min' hsupport)).Nonempty
  · rw [ArchimedeanClass.mk_sum hsupport' (hmono.mono (by simp))]
    rw [HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum seed (f _).prop (by
      simpa using (Finset.mem_erase.mp <| (f.support.erase _).min'_mem hsupport').2)]
    apply Finset.min'_lt_of_mem_erase_min' (α := FiniteArchimedeanClass M)
    apply Finset.min'_mem _ _
  · -- special case: `f` has a single term, and becomes 0 after removing it
    simpa [hsupport'] using (f.support.min' hsupport).2.lt_top

