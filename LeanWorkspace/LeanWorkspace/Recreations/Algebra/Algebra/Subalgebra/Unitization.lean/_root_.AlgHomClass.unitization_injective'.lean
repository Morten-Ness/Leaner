import Mathlib

theorem _root_.AlgHomClass.unitization_injective' {F R S A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h : ∀ r, r ≠ 0 → algebraMap R A r ∉ s)
    [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  induction x with
  | inl_add_inr r a =>
    simp_rw [map_add, hf, ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes] at hx
    rw [add_eq_zero_iff_eq_neg] at hx ⊢
    by_cases hr : r = 0
    · ext
      · simp [hr]
      · simpa [hr] using hx
    · exact (h r hr <| hx ▸ (neg_mem a.property)).elim

