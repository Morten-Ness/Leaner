import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKInjective_of_injective (L : CochainComplex C ℤ) (d : ℤ)
    [L.IsStrictlyGE d] [∀ (n : ℤ), Function.Injective (L.X n)] :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `CochainComplex.isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : ℕ) : Set (Cochain K L (-1)) :=
      setOf (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp ↦
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : ℕ) (α : X n) : X (n + 1) :=
      ⟨_, (CochainComplex.isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]

