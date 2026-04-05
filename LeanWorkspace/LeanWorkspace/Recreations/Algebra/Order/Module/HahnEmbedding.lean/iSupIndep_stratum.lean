import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

theorem iSupIndep_stratum : iSupIndep u.stratum := by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congr(ArchimedeanClass.mk $hf)
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases! hnonempty : f.support.Nonempty
  · have hmem (x : FiniteArchimedeanClass M) : (f x).val ∈ u.stratum x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      change ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum u (hmem x) (by simpa using hx)]
      rw [HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum u (hmem y) (by simpa using hy)]
      exact hxy
    rw [ArchimedeanClass.mk_sum hnonempty hmono, HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum u (hmem _)
      (by simpa using f.support.min'_mem hnonempty), ← val_mk h0, Subtype.coe_ne_coe]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    have := HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum u ha h0
    rw [← val_mk h0, ← Subtype.ext_iff] at this
    simpa [DFinsupp.notMem_support_iff, this] using (f c).prop
  · rw [hnonempty]
    symm
    simpa using h0

