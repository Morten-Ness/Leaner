import Mathlib

variable {M : Type*}

theorem Irreducible.isRelPrime_iff_not_dvd [Monoid M] {p n : M} (hp : Irreducible p) :
    IsRelPrime p n ↔ ¬ p ∣ n := by
  refine ⟨fun h contra ↦ hp.not_isUnit (h dvd_rfl contra), fun hpn d hdp hdn ↦ ?_⟩
  contrapose! hpn
  suffices Associated p d from Associated.trans this.dvd hdn
  exact (hp.dvd_iff.mp hdp).resolve_left hpn

