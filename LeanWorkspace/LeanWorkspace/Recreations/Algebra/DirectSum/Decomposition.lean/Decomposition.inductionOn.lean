import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem Decomposition.inductionOn {motive : M → Prop} (zero : motive 0)
    (homogeneous : ∀ {i} (m : ℳ i), motive (m : M))
    (add : ∀ m m' : M, motive m → motive m' → motive (m + m')) : ∀ m, motive m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  haveI t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (DirectSum.decompose ℳ).left_inv _
      right_inv := fun _ ↦ (DirectSum.decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (DirectSum.Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ homogeneous ⟨m, h⟩) zero add
--  exact fun m ↦
--    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add

