import Mathlib

variable {K L M : Type*}

variable [Field K] [LieRing L] [LieAlgebra K L]

variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]

variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)

variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)

theorem isSemisimple_of_nondegenerate : IsSemisimple K L := by
  refine ⟨?_, ?_, hL⟩
  · simpa using LieAlgebra.InvariantForm.atomistic Φ hΦ_nondeg hΦ_inv hΦ_refl hL ⊤
  intro I hI
  apply (LieAlgebra.InvariantForm.orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).mono_right
  apply sSup_le
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, and_imp]
  intro J hJ hJI
  rw [← lie_eq_self_of_isAtom_of_nonabelian J hJ (hL J hJ), lieIdeal_oper_eq_span, lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [orthogonal_carrier, Φ.isOrtho_def, Set.mem_setOf_eq]
  intro z hz
  rw [← neg_eq_zero, ← hΦ_inv]
  suffices ⁅(x : L), z⁆ = 0 by simp only [this, map_zero, LinearMap.zero_apply]
  rw [← LieSubmodule.mem_bot (R := K) (L := L), ← (hJ.disjoint_of_ne hI hJI).eq_bot]
  apply lie_le_inf
  exact lie_mem_lie x.2 hz

