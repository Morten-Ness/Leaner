import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι → M') :
    ∃ b : S, ∀ i ∈ s, IsLocalizedModule.IsInteger f (b.val • g i) := by
  classical
  choose sec hsec using (fun i ↦ IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i ∈ s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finset_prod]
    rw [← hsec, ← mul_smul, Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finset_prod, mul_comm]
    rw [← Finset.prod_insert (f := fun i ↦ ((sec i).snd).val) (s.notMem_erase i),
      Finset.insert_erase hi]

