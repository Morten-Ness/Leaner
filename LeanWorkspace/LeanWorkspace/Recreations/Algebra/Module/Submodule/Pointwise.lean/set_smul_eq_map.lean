import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem set_smul_eq_map [SMulCommClass R R N] :
    sR • N =
    Submodule.map
      (N.subtype.comp (Finsupp.lsum R <| DistribSMul.toLinearMap _ _))
      (Finsupp.supported N R sR) := by
  classical
  apply Submodule.set_smul_eq_of_le
  · intro r n hr hn
    exact ⟨Finsupp.single r ⟨n, hn⟩, Finsupp.single_mem_supported _ _ hr, by simp⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    simp only [LinearMap.coe_comp, coe_subtype, Finsupp.coe_lsum, Finsupp.sum, Function.comp_apply]
    rw [AddSubmonoid.coe_finset_sum]
    refine Submodule.sum_mem (p := sR • N) (t := c.support) ?_ _ ⟨sR • N, ?_⟩
    · rintro r hr
      rw [Submodule.mem_set_smul_def, Submodule.mem_sInf]
      rintro p hp
      exact hp (hc hr) (c r).2
    · ext x : 1
      simp only [Set.mem_iInter, SetLike.mem_coe]
      fconstructor
      · refine fun h ↦ h fun r n hr hn ↦ ?_
        rw [Submodule.mem_set_smul_def, mem_sInf]
        exact fun p hp ↦ hp hr hn
      · simp_all

