import Mathlib

open scoped Relator

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem rel_map_of_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Archimedean G] [AddGroup H]
    [AddConstMapClass F G H a b] {f : F} {R : H → H → Prop} [IsTrans H R]
    [hR : CovariantClass H H (fun x y ↦ y + x) R] (ha : 0 < a) {l : G}
    (hf : ∀ x ∈ Icc l (l + a), ∀ y ∈ Icc l (l + a), x < y → R (f x) (f y)) :
    ((· < ·) ⇒ R) f f := fun x y hxy ↦ by
  replace hR := hR.elim
  have ha' : 0 ≤ a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x ∈ Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa using hR (m • b) this
    exact this _ _ (by simpa) hm
  · -- Now find `n` such that `l + n • a < y ≤ l + (n + 1) • a`
    rcases existsUnique_sub_zsmul_mem_Ioc ha y l with ⟨n, hny, -⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · -- Since `l ≤ x ≤ y`, the case `n < 0` is impossible
      refine absurd ?_ hxy.not_ge
      calc
        y ≤ l + a + n • a := sub_le_iff_le_add.1 hny.2
        _ = l + (n + 1) • a := by rw [add_comm n, add_smul, one_smul, add_assoc]
        _ ≤ l + (0 : ℤ) • a := by gcongr; lia
        _ ≤ x := by simpa using hx.1
    · -- If `n = 0`, then `l < y ≤ l + a`, hence we can apply the assumption
      exact hf x (Ico_subset_Icc_self hx) y (by simpa using Ioc_subset_Icc_self hny) hxy
    · -- In the remaining case `0 < n` we use transitivity.
      -- If `R = (· < ·)`, then the proof looks like
      -- `f x < f (l + a) ≤ f (l + n • a) < f y`
      trans f (l + (1 : ℤ) • a)
      · grind
      have hy : R (f (l + n • a)) (f y) := by
        rw [← sub_add_cancel y (n • a), AddConstMapClass.map_add_zsmul, AddConstMapClass.map_add_zsmul]
        refine hR _ <| hf _ ?_ _ (Ioc_subset_Icc_self hny) hny.1; simpa
      rw [← Int.add_one_le_iff, zero_add] at hn
      rcases hn.eq_or_lt with rfl | hn; · assumption
      trans f (l + n • a)
      · refine Int.rel_of_forall_rel_succ_of_lt R (f := (f <| l + · • a)) (fun k ↦ ?_) hn
        simp_rw [add_comm k 1, add_zsmul, ← add_assoc, one_zsmul, AddConstMapClass.map_add_zsmul]
        refine hR (k • b) (hf _ ?_ _ ?_ ?_) <;> simpa
      · assumption

