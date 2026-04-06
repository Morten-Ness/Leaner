import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0 := by
  constructor
  · intro h
    refine ⟨(a0, b0), ?_, ?_⟩
    · exact ⟨Finset.mem_product.mpr ⟨aA, bB⟩, rfl⟩
    · intro ab hab
      rcases hab with ⟨habAB, habmul⟩
      rcases Finset.mem_product.mp habAB with ⟨ha, hb⟩
      rcases h ha hb habmul with ⟨rfl, rfl⟩
      rfl
  · rintro ⟨ab, hab, habuniq⟩
    rcases ab with ⟨a, b⟩
    rcases hab with ⟨habAB, habmul⟩
    rcases Finset.mem_product.mp habAB with ⟨ha, hb⟩
    have hEq : (a0, b0) = (a, b) := habuniq (a0, b0) ⟨Finset.mem_product.mpr ⟨aA, bB⟩, by simpa [Prod.fst, Prod.snd] using habmul.symm⟩
    rcases Prod.mk.inj hEq.symm with ⟨rfl, rfl⟩
    intro x y hx hy hxy
    have hpair : (x, y) = (a, b) := habuniq (x, y) ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩
    exact Prod.mk.inj hpair
