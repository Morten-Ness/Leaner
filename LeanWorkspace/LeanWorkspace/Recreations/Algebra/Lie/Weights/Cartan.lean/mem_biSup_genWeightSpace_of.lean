import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem mem_biSup_genWeightSpace_of {s : Set (H → R)} (hs : ∀ᵉ (χ₁ ∈ s) (χ₂ ∈ s), χ₁ + χ₂ ∈ s)
    {x : L} {m : M} (hx : x ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace H χ)
    (hm : m ∈ ⨆ χ, ⨆ (_ : χ ∈ s), genWeightSpace M χ) :
    ⁅x, m⁆ ∈ ⨆ χ, ⨆ (_ : χ ∈ s), genWeightSpace M χ := by
  induction hx using LieSubmodule.iSup_induction' with
  | zero => simp
  | add _ _ _ _ hu hv => rw [add_lie]; exact add_mem hu hv
  | mem χ₁ u hu =>
    by_cases hχ₁ : χ₁ ∈ s; swap
    · simp_all
    replace hu : u ∈ rootSpace H χ₁ := by simpa [hχ₁] using hu
    induction hm using LieSubmodule.iSup_induction' with
    | zero => simp
    | add _ _ _ _ hv hw => rw [lie_add]; exact add_mem hv hw
    | mem χ₂ v hv =>
      by_cases hχ₂ : χ₂ ∈ s; swap
      · simp_all
      apply LieSubmodule.mem_iSup_of_mem (χ₁ + χ₂)
      simp_all [LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace]

