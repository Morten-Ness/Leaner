import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem finrank_vectorSpan_image_finset_le [DecidableEq P] (p : ι → P) (s : Finset ι) {n : ℕ}
    (hc : #s = n + 1) : finrank k (vectorSpan k (s.image p : Set P)) ≤ n := by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.image_nonempty, ← Finset.card_pos, hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fun p => p -ᵥ p₁)) ?_
  rw [Finset.card_image_of_injective _ (vsub_left_injective p₁), Finset.card_erase_of_mem hp₁,
    tsub_le_iff_right, ← hc]
  apply Finset.card_image_le

