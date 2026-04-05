import Mathlib

theorem bddAbove_range_mul {α β : Type*} [Nonempty α] {u v : α → β} [Preorder β] [Zero β] [Mul β]
    [PosMulMono β] [MulPosMono β] (hu : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv : BddAbove (Set.range v)) (hv0 : 0 ≤ v) : BddAbove (Set.range (u * v)) := letI : Zero (β × β) := ⟨(0, 0)⟩
  BddAbove.range_comp_of_nonneg (f := fun i ↦ (u i, v i)) (g := fun x ↦ x.1 * x.2)
    (bddAbove_range_prod.mpr ⟨hu, hv⟩) (fun x ↦ ⟨hu0 x, hv0 x⟩) ((monotone_fst.monotoneOn _).mul
      (monotone_snd.monotoneOn _) (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.2))

