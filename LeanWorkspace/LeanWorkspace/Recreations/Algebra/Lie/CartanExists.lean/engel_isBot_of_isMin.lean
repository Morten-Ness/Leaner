import Mathlib

open scoped Polynomial

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

set_option backward.isDefEq.respectTransparency false in
theorem engel_isBot_of_isMin (hLK : finrank K L ≤ #K) (U : LieSubalgebra K L)
    (E : {engel K x | x ∈ U}) (hUle : U ≤ E) (hmin : IsMin E) :
    IsBot E := by
  rcases E with ⟨_, x, hxU, rfl⟩
  rintro ⟨_, y, hyU, rfl⟩
  -- It will be useful to repackage the Engel subalgebras
  set Ex : {engel K x | x ∈ U} := ⟨engel K x, x, hxU, rfl⟩
  set Ey : {engel K y | y ∈ U} := ⟨engel K y, y, hyU, rfl⟩
  replace hUle : U ≤ Ex := hUle
  replace hmin : ∀ E, E ≤ Ex → Ex ≤ E := @hmin
  -- We also repackage the Engel subalgebra `engel K x`
  -- as Lie submodule `E` of `L` over the Lie algebra `U`.
  let E : LieSubmodule K U L :=
  { engel K x with
    lie_mem := by rintro ⟨u, hu⟩ y hy; exact (engel K x).lie_mem (hUle hu) hy }
  -- We may and do assume that `x ≠ 0`, since otherwise the statement is trivial.
  obtain rfl | hx₀ := eq_or_ne x 0
  · simpa [Ex, Ey] using hmin Ey
  -- We denote by `Q` the quotient `L / E`, and by `r` the dimension of `E`.
  let Q := L ⧸ E
  let r := finrank K E
  -- If `r = finrank K L`, then `E = L`, and the statement is trivial.
  obtain hr | hr : r = finrank K L ∨ r < finrank K L := (Submodule.finrank_le _).eq_or_lt
  · suffices engel K y ≤ engel K x from hmin Ey this
    suffices engel K x = ⊤ by simp_rw [this, le_top]
    apply LieSubalgebra.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq hr
  -- So from now on, we assume that `r < finrank K L`.
  -- We denote by `x'` and `y'` the elements `x` and `y` viewed as terms of `U`.
  set x' : U := ⟨x, hxU⟩
  set y' : U := ⟨y, hyU⟩
  -- Let `u : U` denote `y - x`.
  let u : U := y' - x'
  -- We denote by `χ r` the characteristic polynomial of `⁅r • u + x, _⁆`
  --   viewed as endomorphism of `E`. Note that `χ` is polynomial in its argument `r`.
  -- Similarly: `ψ r` is the characteristic polynomial of `⁅r • u + x, _⁆`
  --   viewed as endomorphism of `Q`. Note that `ψ` is polynomial in its argument `r`.
  let χ : Polynomial (K[X]) := LieAlgebra.engel_isBot_of_isMin.lieCharpoly K E x' u
  let ψ : Polynomial (K[X]) := LieAlgebra.engel_isBot_of_isMin.lieCharpoly K Q x' u
  -- It suffices to show that `χ` is the monomial `Polynomial.X ^ r`.
  suffices χ = Polynomial.X ^ r by
    -- Indeed, by evaluating the coefficients at `1`
    apply_fun (fun p ↦ p.map (evalRingHom 1)) at this
    -- we find that the characteristic polynomial `χ 1` of `⁅y, _⁆` is equal to `Polynomial.X ^ r`
    simp_rw [Polynomial.map_pow, map_X, χ, LieAlgebra.engel_isBot_of_isMin.lieCharpoly_map_eval, one_smul, u, sub_add_cancel,
      -- and therefore the endomorphism `⁅y, _⁆` acts nilpotently on `E`.
      r, LinearMap.charpoly_eq_X_pow_iff,
      Subtype.ext_iff, coe_toEnd_pow _ _ _ E, ZeroMemClass.coe_zero] at this
    -- We ultimately want to show `engel K x ≤ engel K y`
    intro z hz
    -- which holds by definition of Engel subalgebra and the nilpotency that we just established.
    rw [mem_engel_iff]
    exact this ⟨z, hz⟩
  -- To show that `χ = Polynomial.X ^ r`, it suffices to show that all coefficients in degrees `< r` are `0`.
  suffices ∀ i < r, χ.coeff i = 0 by
    simp_rw [r, ← LieAlgebra.engel_isBot_of_isMin.lieCharpoly_natDegree K E x' u] at this ⊢
    rw [(LieAlgebra.engel_isBot_of_isMin.lieCharpoly_monic K E x' u).eq_X_pow_iff_natDegree_le_natTrailingDegree]
    exact le_natTrailingDegree (LieAlgebra.engel_isBot_of_isMin.lieCharpoly_monic K E x' u).ne_zero this
  -- Let us consider the `i`-th coefficient of `χ`, for `i < r`.
  intro i hi
  -- We separately consider the case `i = 0`.
  obtain rfl | hi0 := eq_or_ne i 0
  · -- `The polynomial `coeff χ 0` is zero if it evaluates to zero on all elements of `K`,
    -- provided that its degree is strictly less than `#K`.
    apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ _ ?deg
    case deg =>
      -- We need to show `(natDegree (coeff χ 0)) < #K` and know that `finrank K L ≤ #K`
      apply lt_of_lt_of_le _ hLK
      rw [Nat.cast_lt]
      -- So we are left with showing `natDegree (coeff χ 0) < finrank K L`
      apply lt_of_le_of_lt _ hr
      apply LieAlgebra.engel_isBot_of_isMin.lieCharpoly_coeff_natDegree _ _ _ _ 0 r (zero_add r)
    -- Fix an element of `K`.
    intro α
    -- We want to show that `α` is a root of `coeff χ 0`.
    -- So we need to show that there is a `z ≠ 0` in `E` satisfying `⁅α • u + x, z⁆ = 0`.
    rw [← coe_evalRingHom, ← coeff_map, LieAlgebra.engel_isBot_of_isMin.lieCharpoly_map_eval,
      ← constantCoeff_apply, LinearMap.charpoly_constantCoeff_eq_zero_iff]
    -- We consider `z = α • u + x`, and split into the cases `z = 0` and `z ≠ 0`.
    let z := α • u + x'
    obtain hz₀ | hz₀ := eq_or_ne z 0
    · -- If `z = 0`, then `⁅α • u + x, x⁆` vanishes and we use our assumption `x ≠ 0`.
      refine ⟨⟨x, self_mem_engel K x⟩, ?_, ?_⟩
      · exact Subtype.coe_ne_coe.mp hx₀
      · dsimp only [z] at hz₀
        simp only [hz₀, map_zero, LinearMap.zero_apply]
    -- If `z ≠ 0`, then `⁅α • u + x, z⁆` vanishes per axiom of Lie algebras
    refine ⟨⟨z, hUle z.2⟩, ?_, ?_⟩
    · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero, Subtype.ext_iff] using hz₀
    · change ⁅z, _⁆ = (0 : E)
      ext
      exact lie_self z.1
  -- We are left with the case `i ≠ 0`, and want to show `coeff χ i = 0`.
  -- We will do this once again by showing that `coeff χ i` vanishes
  -- on a sufficiently large subset `s` of `K`.
  -- But we first need to get our hands on that subset `s`.
  -- We start by observing that `ψ` has non-trivial constant coefficient.
  have hψ : constantCoeff ψ ≠ 0 := by
    -- Suppose that `ψ` in fact has trivial constant coefficient.
    intro H
    -- Then there exists a `z ≠ 0` in `Q` such that `⁅x, z⁆ = 0`.
    obtain ⟨z, hz0, hxz⟩ : ∃ z : Q, z ≠ 0 ∧ ⁅x', z⁆ = 0 := by
      -- Indeed, if the constant coefficient of `ψ` is trivial,
      -- then `0` is a root of the characteristic polynomial of `⁅0 • u + x, _⁆` acting on `Q`,
      -- and hence we find an eigenvector `z` as desired.
      apply_fun (evalRingHom 0) at H
      rw [constantCoeff_apply, ← coeff_map, LieAlgebra.engel_isBot_of_isMin.lieCharpoly_map_eval,
        ← constantCoeff_apply, map_zero, LinearMap.charpoly_constantCoeff_eq_zero_iff] at H
      simpa only [coe_bracket_of_module, ne_eq, zero_smul, zero_add, toEnd_apply_apply]
        using H
    -- It suffices to show `z = 0` (in `Q`) to obtain a contradiction.
    apply hz0
    -- We replace `z : Q` by a representative in `L`.
    obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E z
    -- The assumption `⁅x, z⁆ = 0` is equivalent to `⁅x, z⁆ ∈ E`.
    have : ⁅x, z⁆ ∈ E := by rwa [← LieSubmodule.Quotient.mk_eq_zero']
    -- From this we deduce that there exists an `n` such that `⁅x, _⁆ ^ n` vanishes on `⁅x, z⁆`.
    -- On the other hand, our goal is to show `z = 0` in `Q`,
    -- which is equivalent to showing that `⁅x, _⁆ ^ n` vanishes on `z`, for some `n`.
    simp only [LieSubmodule.mem_mk_iff', LieSubalgebra.mem_toSubmodule, mem_engel_iff,
      LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero', E, Q] at this ⊢
    -- Hence we win.
    obtain ⟨n, hn⟩ := this
    use n + 1
    rwa [pow_succ]
  -- Now we find a subset `s` of `K` of size `≥ r`
  -- such that `constantCoeff ψ` takes non-zero values on all of `s`.
  -- This turns out to be the subset that we alluded to earlier.
  obtain ⟨s, hs, hsψ⟩ : ∃ s : Finset K, r ≤ s.card ∧ ∀ α ∈ s, (constantCoeff ψ).eval α ≠ 0 := by
    classical
    -- Let `t` denote the set of roots of `constantCoeff ψ`.
    let t := (constantCoeff ψ).roots.toFinset
    -- We show that `t` has cardinality at most `finrank K L - r`.
    have ht : t.card ≤ finrank K L - r := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (card_roots' _).trans ?_
      rw [constantCoeff_apply]
      -- Indeed, `constantCoeff ψ` has degree at most `finrank K Q = finrank K L - r`.
      apply LieAlgebra.engel_isBot_of_isMin.lieCharpoly_coeff_natDegree
      suffices finrank K Q + r = finrank K L by rw [← this, zero_add, Nat.add_sub_cancel]
      apply Submodule.finrank_quotient_add_finrank
    -- Hence there exists a subset of size `≥ r` in the complement of `t`,
    -- and `constantCoeff ψ` takes non-zero values on all of this subset.
    obtain ⟨s, hs⟩ := exists_finset_le_card K _ hLK
    use s \ t
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (Finset.le_card_sdiff _ _)
      lia
    · intro α hα
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset, mem_roots', IsRoot.def, not_and, t] at hα
      exact hα.2 hψ
  -- So finally we can continue our proof strategy by showing that `coeff χ i` vanishes on `s`.
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s _ ?hcard
  case hcard =>
    -- We need to show that `natDegree (coeff χ i) < s.card`
    -- Which follows from our assumptions `i < r` and `r ≤ s.card`
    -- and the fact that the degree of `coeff χ i` is less than or equal to `r - i`.
    apply lt_of_le_of_lt (LieAlgebra.engel_isBot_of_isMin.lieCharpoly_coeff_natDegree _ _ _ _ i (r - i) _)
    · lia
    · dsimp only [r] at hi ⊢
      rw [Nat.add_sub_cancel' hi.le]
  -- We need to show that for all `α ∈ s`, the polynomial `coeff χ i` evaluates to zero at `α`.
  intro α hα
  -- Once again, we are left with showing that `⁅y, _⁆` acts nilpotently on `E`.
  rw [← coe_evalRingHom, ← coeff_map, LieAlgebra.engel_isBot_of_isMin.lieCharpoly_map_eval,
    (LinearMap.charpoly_eq_X_pow_iff _).mpr, coeff_X_pow, if_neg hi.ne]
  -- To do so, it suffices to show that the Engel subalgebra of `v = a • u + x` is contained in `E`.
  let v := α • u + x'
  suffices engel K (v : L) ≤ engel K x by
    -- Indeed, in that case the minimality assumption on `E` implies
    -- that `E` is contained in the Engel subalgebra of `v`.
    replace this : engel K x ≤ engel K (v : L) := (hmin ⟨_, v, v.2, rfl⟩ this).ge
    intro z
    -- And so we are done, by the definition of Engel subalgebra.
    simpa only [mem_engel_iff, Subtype.ext_iff, coe_toEnd_pow _ _ _ E] using this z.2
  -- Now we are in good shape.
  -- Fix an element `z` in the Engel subalgebra of `y`.
  intro z hz
  -- We need to show that `z` is in `E`, or alternatively that `z = 0` in `Q`.
  change z ∈ E
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  -- We denote the image of `z` in `Q` by `z'`.
  set z' : Q := LieSubmodule.Quotient.mk' E z
  -- First we observe that `z'` is killed by a power of `⁅v, _⁆`.
  have hz' : ∃ n : ℕ, (toEnd K U Q v ^ n) z' = 0 := by
    rw [mem_engel_iff] at hz
    obtain ⟨n, hn⟩ := hz
    use n
    apply_fun LieSubmodule.Quotient.mk' E at hn
    rw [map_zero] at hn
    rw [← hn]
    clear hn
    induction n with
    | zero => simp only [z', pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih]; rfl
  classical
  -- Now let `n` be the smallest power such that `⁅v, _⁆ ^ n` kills `z'`.
  set n := Nat.find hz' with _hn
  have hn : (toEnd K U Q v ^ n) z' = 0 := Nat.find_spec hz'
  -- If `n = 0`, then we are done.
  obtain hn₀ | ⟨k, hk⟩ : n = 0 ∨ ∃ k, n = k + 1 := by cases n <;> simp
  · simpa only [hn₀, pow_zero, Module.End.one_apply] using hn
  -- If `n = k + 1`, then we can write `⁅v, _⁆ ^ n = ⁅v, _⁆ ∘ ⁅v, _⁆ ^ k`.
  -- Recall that `constantCoeff ψ` is non-zero on `α`, and `v = α • u + x`.
  specialize hsψ α hα
  -- Hence `⁅v, _⁆` acts injectively on `Q`.
  rw [← coe_evalRingHom, constantCoeff_apply, ← coeff_map, LieAlgebra.engel_isBot_of_isMin.lieCharpoly_map_eval,
    ← constantCoeff_apply, ne_eq, LinearMap.charpoly_constantCoeff_eq_zero_iff] at hsψ
  -- We deduce from this that `z' = 0`, arguing by contraposition.
  contrapose! hsψ
  -- Indeed `⁅v, _⁆` kills `⁅v, _⁆ ^ k` applied to `z'`.
  use (toEnd K U Q v ^ k) z'
  refine ⟨?_, ?_⟩
  · -- And `⁅v, _⁆ ^ k` applied to `z'` is non-zero by definition of `n`.
    apply Nat.find_min hz'; lia
  · rw [← hn, hk, pow_succ', Module.End.mul_apply]

