import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

set_option backward.isDefEq.respectTransparency false in
theorem cycles_left_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Mono S.f]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (cyclesMap S.f i) (cyclesMap S.g i)
      (by rw [← cyclesMap_comp, S.zero, cyclesMap_zero])).Exact := by
  have : Mono (ShortComplex.map S (eval C c i)).f := by dsimp; infer_instance
  have hi := (hS.map (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc, ← cyclesMap_i, reassoc_of% hk, zero_comp])
    dsimp at H
    refine ⟨S.X₁.liftCycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

