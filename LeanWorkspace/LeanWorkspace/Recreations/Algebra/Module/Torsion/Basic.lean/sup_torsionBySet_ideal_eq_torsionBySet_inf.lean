import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

theorem sup_torsionBySet_ideal_eq_torsionBySet_inf (P Q : Ideal R) {hc : P ⊔ Q = ⊤} :
    Submodule.torsionBySet R M ↑(P) ⊔ Submodule.torsionBySet R M ↑(Q) = Submodule.torsionBySet R M ↑(P ⊓ Q) := by
  let map : Fin 2 → Ideal R | 0 => P | 1 => Q
  have heq := Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf
    (p := map) (M := M) (S := ⊤) ?_
  · have : ⨆ i, ⨆ (_ : i = 0 ∨ i = 1), Submodule.torsionBySet R M ↑(map i) =
        Submodule.torsionBySet R M ↑(map 0) ⊔ Submodule.torsionBySet R M ↑(map 1) := iSup_pair
    simpa [Finset.top_eq_univ, Fin.univ_succ, Fin.isValue, coe_iInf, this] using heq
  · simp_all [Set.pairwise_pair, Fin.univ_succ, map, sup_comm]

