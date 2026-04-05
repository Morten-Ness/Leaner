import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable [IsDomain R]

theorem Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i)
        (e : ι → ℕ), DirectSum.IsInternal fun i => torsionBy R M <| p i ^ e i := by
  classical
  refine ⟨_, ?_, _, _, ?_, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  · exact Finset.fintypeCoeSort _
  · rintro ⟨p, hp⟩
    have hP := prime_of_factor p (Multiset.mem_toFinset.mp hp)
    haveI := Ideal.isPrime_of_prime hP
    exact (IsPrincipal.prime_generator_of_isPrime p hP.ne_zero).irreducible

