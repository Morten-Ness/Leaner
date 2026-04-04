import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sp : AffineSubspace k P}
    [FiniteDimensional k sp.direction] (hle : affineSpan k (s.image p : Set P) ≤ sp)
    (hc : #s = finrank k sp.direction + 1) : affineSpan k (s.image p : Set P) = sp := by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos, hc]
    apply Nat.succ_pos
  refine eq_of_direction_eq_of_nonempty_of_le ?_ ((hn.image p).to_set.affineSpan k) hle
  have hd := direction_le hle
  rw [direction_affineSpan] at hd ⊢
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc

