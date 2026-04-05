import Mathlib

variable (k L M : Type*) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [Module.Finite k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
  [IsIrreducible k L M] [IsFaithful k L M] [IsTriangularizable k L M]

set_option backward.isDefEq.respectTransparency false in
theorem hasCentralRadical_and_of_isIrreducible_of_isFaithful :
    HasCentralRadical k L ∧ (∀ x, x ∈ center k L ↔ toEnd k L M x ∈ k ∙ LinearMap.id) := by
  have _i := nontrivial_of_isIrreducible k L M
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual k (radical k L), Nontrivial (weightSpace M χ) :=
    exists_nontrivial_weightSpace_of_isSolvable k (radical k L) M
  let N : LieSubmodule k L M := weightSpaceOfIsLieTower k M χ
  replace hχ : Nontrivial N := hχ
  replace hχ : N = ⊤ := N.eq_top_of_isIrreducible k L M
  replace hχ (x : L) (hx : x ∈ radical k L) : toEnd k _ M x = χ ⟨x, hx⟩ • LinearMap.id := by
    ext m
    have hm : ∀ (y : L) (hy : y ∈ radical k L), ⁅y, m⁆ = χ ⟨y, hy⟩ • m := by
      simpa [N, weightSpaceOfIsLieTower, mem_weightSpace] using (hχ ▸ mem_top _ : m ∈ N)
    simpa using hm x hx
  have aux : radical k L = center k L := by
    refine le_antisymm (fun x hx ↦ (mem_maxTrivSubmodule k L L x).mpr ?_) (center_le_radical k L)
    intro y
    simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), LieHom.map_lie, hχ _ hx, lie_smul,
      (toEnd k L M y).commute_id_right.lie_eq]
  refine ⟨⟨aux⟩, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ (mem_maxTrivSubmodule k L L x).mpr fun y ↦ ?_⟩⟩
  · rw [← aux] at hx
    exact Submodule.mem_span_singleton.mpr ⟨χ ⟨x, hx⟩, (hχ x hx).symm⟩
  · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), LieHom.map_lie, ← ht, lie_smul,
      (toEnd k L M y).commute_id_right.lie_eq]

