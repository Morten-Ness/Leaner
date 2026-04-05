import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]

variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

theorem IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
    [Module.Finite R M] [Module.FinitePresentation R M'] :
    ∃ r ∈ S, IsLocalizedModule (.powers r) f := by
  have : IsLocalizedModule S (.id (R := R) (M := M')) :=
    ⟨IsLocalizedModule.map_units f, fun y ↦ ⟨⟨y, 1⟩, by simp⟩, by simpa using ⟨1, S.one_mem⟩⟩
  obtain ⟨r, hrp, H⟩ := exists_bijective_map_powers S
      f (.id (R := R) (M := M')) f <| by
    convert show Function.Bijective LinearMap.id from Function.bijective_id
    apply IsLocalizedModule.ext S f
    · exact IsLocalizedModule.map_units f
    · simp [IsLocalizedModule.map_comp]
  have hrp' : .powers r ≤ S := by simpa [Submonoid.powers_le]
  refine ⟨r, hrp, ⟨fun x ↦ IsLocalizedModule.map_units f ⟨x, hrp' x.2⟩, ?_, ?_⟩⟩
  · intro y
    obtain ⟨x, hx⟩ := (H _ dvd_rfl).2 (LocalizedModule.mkLinearMap _ _ y)
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
      (.powers r) (LocalizedModule.mkLinearMap _ _) x
    obtain ⟨m, hm⟩ : ∃ m, r ^ (m + n) • y = f (r ^ m • x) := by
      simpa [LocalizedModule.map, IsLocalizedModule.mk_eq_mk', -IsLocalizedModule.mk'_one,
        pow_add, mul_smul, IsLocalizedModule.mk'_eq_mk'_iff, Submonoid.mem_powers_iff,
        Submonoid.smul_def] using hx
    exact ⟨⟨_, ⟨_, _, rfl⟩⟩, hm⟩
  · exact fun {x₁ x₂} hx ↦ IsLocalizedModule.exists_of_eq (f := LocalizedModule.mkLinearMap
      (.powers r) _) ((H _ dvd_rfl).1 (by simp [hx]))

