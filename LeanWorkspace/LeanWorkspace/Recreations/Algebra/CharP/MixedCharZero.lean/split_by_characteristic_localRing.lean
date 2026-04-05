import Mathlib

variable (R : Type*) [CommRing R]

variable {P : Prop}

private theorem of_algebraRat [Algebra ℚ R] : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine I.eq_top_of_isUnit_mem ?_ (IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 (a - b : ℚ) ?_))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
  simpa only [Ne, sub_eq_zero] using (@Nat.cast_injective ℚ _ _).ne hI


private theorem PNat.isUnit_natCast [h : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : IsUnit (n : R) := by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply h_char_zero.cast_injective.ne n.ne_zero
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)


private noncomputable def pnatCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ℕ+ → Rˣ := fun n => (PNat.isUnit_natCast n).unit

private noncomputable instance coePNatUnits
    [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : Coe ℕ+ Rˣ :=
  ⟨EqualCharZero.pnatCast⟩


private theorem pnatCast_one [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] :
    ((1 : ℕ+) : Rˣ) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  rw [PNat.one_coe, Nat.cast_one]


private theorem pnatCast_eq_natCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] (n : ℕ+) :
    ((n : Rˣ) : R) = ↑n := by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  simp only [IsUnit.unit_spec]


private noncomputable def algebraRat (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    Algebra ℚ R := haveI : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [← divp_assoc, divp_mul_eq_mul_divp, divp_divp_eq_divp_mul, divp_eq_iff_mul_eq,
        pnatCast_eq_natCast, Rat.coe_pnatDen, Units.val_mul]
      trans (↑((a * b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.mul_num_den' a b]
      simp
    map_add' := by
      intro a b
      simp only [Units.add_divp, pnatCast_eq_natCast, Rat.coe_pnatDen, divp_mul_eq_mul_divp,
        Units.divp_add, divp_divp_eq_divp_mul, divp_eq_iff_mul_eq, Units.val_mul]
      trans (↑((a + b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.add_num_den' a b]
      simp }


private theorem of_not_mixedCharZero [CharZero R] (h : ∀ p > 0, ¬MixedCharZero R p) :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI_ne_top
  suffices CharP (R ⧸ I) 0 from CharP.charP_to_charZero _
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.succ_pos)


private theorem to_not_mixedCharZero (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    ∀ p > 0, ¬MixedCharZero R p := by
  intro p p_pos
  by_contra hp_mixedChar
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)


theorem split_by_characteristic_localRing [IsLocalRing R]
    (h_pos : ∀ p : ℕ, IsPrimePow p → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : ℕ) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char

