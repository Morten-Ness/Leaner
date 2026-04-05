import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem normalizer_eq_self_of_engel_le [IsArtinian R L]
    (H : LieSubalgebra R L) (x : L) (h : LieSubalgebra.engel R x ≤ H) :
    normalizer H = H := by
  set N := normalizer H
  apply le_antisymm _ (le_normalizer H)
  calc N.toSubmodule ≤ (LieSubalgebra.engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : ∀ n ∈ N, ⁅x, n⁆ ∈ H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (LieSubalgebra.self_mem_engel R x))
    rwa [← lie_skew, neg_mem_iff (G := L)]
  have aux₂ : ∀ n ∈ N, ⁅x, n⁆ ∈ N := fun n hn ↦ le_normalizer H (aux₁ _ hn)
  let dx : N →ₗ[R] N := (ad R L x).restrict aux₂
  obtain ⟨k, hk⟩ : ∃ a, ∀ b ≥ a, Codisjoint (LinearMap.ker (dx ^ b)) (LinearMap.range (dx ^ b)) :=
    eventually_atTop.mp <| dx.eventually_codisjoint_ker_pow_range_pow
  specialize hk (k + 1) (Nat.le_add_right k 1)
  rw [← Submodule.map_subtype_top N.toSubmodule, Submodule.map_le_iff_le_comap]
  apply hk
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_left
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    simp only [Submodule.mem_comap, LieSubalgebra.mem_engel_iff, mem_toSubmodule]
    use k + 1
    clear hk; revert hy
    generalize k + 1 = k
    induction k generalizing y with
    | zero =>
      cases y; intro hy; simp only [pow_zero, Module.End.one_apply]
      exact (AddSubmonoid.mk_eq_zero N.toAddSubmonoid).mp hy
    | succ k ih => solve_by_elim
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_right
    rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨y, rfl⟩
    simp only [pow_succ', Module.End.mul_apply, Submodule.mem_comap, mem_toSubmodule]
    apply aux₁
    simp only [Submodule.coe_subtype, SetLike.coe_mem]

