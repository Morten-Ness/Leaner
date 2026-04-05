import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type v} [AddCommGroup M] [Module R M]

variable [IsDedekindDomain R]

theorem isInternal_prime_power_torsion [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBySet R M (p ^ (factors (⊤ : Submodule R M).annihilator).count ↑p : Ideal R) := by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

