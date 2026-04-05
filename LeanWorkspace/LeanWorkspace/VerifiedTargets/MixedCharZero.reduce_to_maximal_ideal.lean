import Mathlib

variable (R : Type*) [CommRing R]

theorem reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  constructor
  · intro g
    rcases g with ⟨I, ⟨hI_not_top, _⟩⟩
    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM_ge⟩⟩
    use M
    constructor
    · exact hM_max
    · cases CharP.exists (R ⧸ M) with
      | intro r hr =>
        convert hr
        have r_dvd_p : r ∣ p := by
          rw [← CharP.cast_eq_zero_iff (R ⧸ M) r p]
          convert congr_arg (Ideal.Quotient.factor hM_ge) (CharP.cast_eq_zero (R ⧸ I) p)
        symm
        apply (Nat.Prime.eq_one_or_self_of_dvd hp r r_dvd_p).resolve_left
        exact CharP.char_ne_one (R ⧸ M) r
  · intro ⟨I, hI_max, h_charP⟩
    use I
    exact ⟨Ideal.IsMaximal.ne_top hI_max, h_charP⟩

