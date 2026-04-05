import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
    {a : ι → M} :
    StrictMonoOn (MulArchimedeanClass.mk ∘ a) s → MulArchimedeanClass.mk (∏ i ∈ s, (a i)) = MulArchimedeanClass.mk (a (s.min' hnonempty)) := by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs ∈ (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (Finset.min'_mem _ _)
    have hne : MulArchimedeanClass.mk (a i) ≠ MulArchimedeanClass.mk (a (s.min' hs)) := by
      by_contra h
      obtain eq := hmono.injOn (by simp) hminmem h
      rw [eq] at hi
      exact hi (Finset.min'_mem _ hs)
    rw [← ih] at hne
    obtain hlt | hlt := lt_or_gt_of_ne hne
    · rw [MulArchimedeanClass.mk_mul_eq_mk_left hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, MulArchimedeanClass.mk_mul_eq_mk_left hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · apply ((hmono.lt_iff_lt hminmem (by simp)).mp ?_).le
        rw [ih] at hlt
        exact hlt
      · exact Finset.min'_le _ _ hmem

