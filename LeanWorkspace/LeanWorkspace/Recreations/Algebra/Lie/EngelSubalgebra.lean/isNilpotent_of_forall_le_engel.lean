import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem isNilpotent_of_forall_le_engel [IsNoetherian R L]
    (H : LieSubalgebra R L) (h : ∀ x ∈ H, H ≤ LieSubalgebra.engel R x) :
    LieRing.IsNilpotent H := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := R)]
  intro x
  let K : ℕ →o Submodule R H :=
    ⟨fun n ↦ LinearMap.ker ((ad R H x) ^ n), fun m n hmn ↦ ?mono⟩
  case mono =>
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact Module.End.pow_map_zero_of_le hmn hy
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  use n
  ext y
  rw [coe_ad_pow]
  specialize h x x.2 y.2
  rw [LieSubalgebra.mem_engel_iff] at h
  obtain ⟨m, hm⟩ := h
  obtain (hmn | hmn) : m ≤ n ∨ n ≤ m := le_total m n
  · exact Module.End.pow_map_zero_of_le hmn hm
  · have : ∀ k : ℕ, ((ad R L) x ^ k) y = 0 ↔ y ∈ K k := by simp [K, Subtype.ext_iff, coe_ad_pow]
    rwa [this, ← hn m hmn, ← this] at hm

