import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem _root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one [IsDomain R] [Ring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : Irreducible p) (hdeg : p.natDegree ≠ 1) {x : S}
    (hx : x ∈ (algebraMap R S).range) : p.aeval x ≠ 0 := by
  obtain ⟨_, rfl⟩ := hx
  rw [aeval_algebraMap_apply_eq_algebraMap_eval]
  exact fun heq ↦ hp.not_isRoot_of_natDegree_ne_one hdeg <|
    FaithfulSMul.algebraMap_injective _ _ <| map_zero (algebraMap R S) ▸ heq

