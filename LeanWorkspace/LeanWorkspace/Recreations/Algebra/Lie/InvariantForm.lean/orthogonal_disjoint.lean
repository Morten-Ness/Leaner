import Mathlib

variable {R L M : Type*}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L)

variable [LieAlgebra R L]

theorem orthogonal_disjoint
    (Φ : LinearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L)
    -- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
    (hL : ∀ I : LieIdeal R L, IsAtom I → ¬IsLieAbelian I)
    (I : LieIdeal R L) (hI : IsAtom I) :
    Disjoint I (LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv I) := by
  rw [disjoint_iff, ← hI.lt_iff, lt_iff_le_and_ne]
  suffices ¬I ≤ LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv I by simpa
  intro contra
  apply hI.1
  rw [eq_bot_iff, ← lie_eq_self_of_isAtom_of_nonabelian I hI (hL I hI),
      LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg.1
  intro z
  rw [hΦ_inv, neg_eq_zero]
  have hyz : ⁅(x : L), z⁆ ∈ I := lie_mem_left _ _ _ _ _ x.2
  exact contra hyz y y.2

