import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) :
    affineSpan k (Set.range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1 := by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn, ← finrank_top, ← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot,
      ← hi.finrank_vectorSpan hn]
  · intro hc
    rw [← finrank_top, ← direction_top k V P] at hc
    exact hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one le_top hc

