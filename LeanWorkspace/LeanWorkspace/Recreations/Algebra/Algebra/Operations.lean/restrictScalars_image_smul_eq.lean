import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

theorem restrictScalars_image_smul_eq {S M : Type*}
    [CommSemiring S] [Algebra S R]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M]
    (s : Set S) (N : Submodule R M) :
    (algebraMap S R '' s • N).restrictScalars S = s • N.restrictScalars S := by
  refine le_antisymm (fun x x_in ↦ ?_) (set_smul_le _ _ _ fun r x r_in x_in ↦ ?_)
  · rw [restrictScalars_mem] at x_in
    refine set_smul_inductionOn x x_in ?_ ?_ (fun _ _ _ _ h h' ↦  add_mem h h') (zero_mem _)
    · rintro _ x ⟨r, r_in, rfl⟩ x_in
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem r_in x_in
    · intro r y h h'
      obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp <| smul_mem _ r h
      simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
      refine sum_mem fun u u_in ↦ ?_
      obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem u_in' (coe_mem (c ((algebraMap S R) u)))
  · rw [restrictScalars_mem, ← algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) x_in

