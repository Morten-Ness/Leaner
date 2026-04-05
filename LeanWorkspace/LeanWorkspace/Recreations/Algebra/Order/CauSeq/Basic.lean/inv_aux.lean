import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_aux {f : CauSeq β abv} (hf : ¬CauSeq.LimZero f) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | _, ε0 =>
    let ⟨_, K0, HK⟩ := CauSeq.abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (CauSeq.cauchy₃ f δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩

