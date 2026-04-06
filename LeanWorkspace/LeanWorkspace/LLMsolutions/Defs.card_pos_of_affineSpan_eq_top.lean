FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem card_pos_of_affineSpan_eq_top {ι : Type*} [Fintype ι] {p : ι → P}
    (h : affineSpan k (Set.range p) = ⊤) : 0 < Fintype.card ι := by
  by_contra hcard
  have h0 : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos hcard
  have hisempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
  letI : IsEmpty ι := hisempty
  have hrange : Set.range p = (∅ : Set P) := by
    ext x
    simp [Set.mem_range]
  rw [hrange] at h
  have hne : (⊥ : AffineSubspace k P) ≠ ⊤ := by
    intro hbt
    let p0 : P := Classical.choice (Classical.decEq P |> fun _ => by infer_instance)
    have : p0 ∈ (⊥ : AffineSubspace k P) := by simpa [hbt]
    simpa using this
  exact hne h.symm
