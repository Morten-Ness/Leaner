import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type v} [AddCommGroup M] [Module R M]

variable [IsDedekindDomain R]

theorem exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsionBySet R M (p ^ e p : Ideal R) := by
  classical
  exact ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    Submodule.isInternal_prime_power_torsion hM⟩

