import Mathlib

open scoped Function

variable (R : Type*)

variable [Ring R] (S : Sequence R)

theorem span_degreeLT {m : ℕ} (hCoeff : ∀ i < m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iio m) = degreeLT R m := by
  apply span_eq_of_le
  · intro P hP
    obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hP
    rw [SetLike.mem_coe, Polynomial.mem_degreeLT, S.degree_eq i, Nat.cast_lt]
    exact Set.mem_Iio.mp hi
  intro P hP
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases! p_ne_zero : P = 0
    · simp [p_ne_zero]
    have hn : n < m := by
      rw [Polynomial.mem_degreeLT] at hP
      have := Polynomial.degree_eq_natDegree p_ne_zero
      aesop
    -- let u be the inverse of `S n`'s leading coefficient
    obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n hn
    -- We'll show `P` is the difference of two terms in the span:
    --   a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    --   and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head ∈ span R (S '' Set.Iio m) := by
      have in_span : S n ∈ span R (S '' Set.Iio m) := subset_span ⟨n, by simp [hn], rfl⟩
      have smul_span := smul_mem (span R (S '' Set.Iio m)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
    apply sub_mem_iff_left _ head_mem_span |>.mp
    -- so let's prove the tail has degree less than `n`
    suffices tail.degree < n by
      refine ih tail.natDegree ((natDegree_lt_iff_degree_lt tail_eq_zero).mpr this) ?_ rfl
      grw [(Nat.cast_lt (α := WithBot ℕ)).mpr hn] at this
      rwa [Polynomial.mem_degreeLT]
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular, IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n hn).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
      ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
    have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree <| by
      grind [degree_eq_bot]
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree p_ne_zero, head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rw [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

