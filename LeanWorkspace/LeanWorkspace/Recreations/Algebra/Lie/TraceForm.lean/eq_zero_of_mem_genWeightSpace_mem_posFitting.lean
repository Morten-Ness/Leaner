import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem eq_zero_of_mem_genWeightSpace_mem_posFitting [LieRing.IsNilpotent L]
    {B : LinearMap.BilinForm R M} (hB : ∀ (x : L) (m n : M), B ⁅x, m⁆ n = -B m ⁅x, n⁆)
    {m₀ m₁ : M} (hm₀ : m₀ ∈ genWeightSpace M (0 : L → R)) (hm₁ : m₁ ∈ posFittingComp R L M) :
    B m₀ m₁ = 0 := by
  replace hB : ∀ x (k : ℕ) m n, B m ((φ x ^ k) n) = (-1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : ∀ m, B m (φ x n) = (-1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← Module.End.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices ∀ (x : L) m, m ∈ posFittingCompOf R M x → B m₀ m = 0 by
    refine LieSubmodule.iSup_induction (motive := fun m ↦ (B m₀) m = 0) _ hm₁ this (map_zero _) ?_
    simp_all
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

