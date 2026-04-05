import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

theorem disjoint_torsionBySet_ideal {P Q : Ideal R} (hc : P ⊔ Q = ⊤) :
    Disjoint (Submodule.torsionBySet R M ↑(P)) (Submodule.torsionBySet R M ↑(Q)) := by
  let map : Fin 2 → Ideal R | 0 => P | 1 => Q
  have heq := Submodule.supIndep_torsionBySet_ideal (p := map) (M := M) (S := ⊤) ?_
  · simpa [Finset.top_eq_univ, Fin.isValue, map] using heq
  · aesop (add norm [Fin.univ_succ, Set.pairwise_pair, map, sup_comm])

