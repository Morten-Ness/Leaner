import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem splits_iff_exists_multiset' {f : R[X]} :
    Polynomial.Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Polynomial.Splits, Submonoid.closure_union, ← hS, Submonoid.closure_eq, Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg, leadingCoeff_mul_monic, leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Polynomial.Splits.C _).mul (.multisetProd (by simp [Polynomial.Splits.X_add_C]))

