import Mathlib

variable (R : Type*) [CommRing R]

theorem reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  constructor
  · intro h q q_prime q_mixedChar
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
  · intro h q q_pos q_mixedChar
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩
    let r := ringChar (R ⧸ M)
    have r_pos : r ≠ 0 := by
      have q_zero :=
        congr_arg (Ideal.Quotient.factor h_IM) (CharP.cast_eq_zero (R ⧸ I) q)
      simp only [map_natCast, map_zero] at q_zero
      apply ne_zero_of_dvd_ne_zero (ne_of_gt q_pos)
      exact (CharP.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero
    have r_prime : Nat.Prime r :=
      or_iff_not_imp_right.1 (CharP.char_is_prime_or_zero (R ⧸ M) r) r_pos
    apply h r r_prime
    have : CharZero R := q_mixedChar.toCharZero
    exact ⟨⟨M, hM_max.ne_top, ringChar.of_eq rfl⟩⟩

