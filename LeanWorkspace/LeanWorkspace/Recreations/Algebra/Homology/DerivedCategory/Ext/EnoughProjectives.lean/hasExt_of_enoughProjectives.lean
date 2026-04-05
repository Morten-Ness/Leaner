import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem hasExt_of_enoughProjectives [LocallySmall.{w} C] [EnoughProjectives C] : HasExt.{w} C := by
  letI := HasDerivedCategory.standard C
  have := hasExt_of_hasDerivedCategory C
  rw [hasExt_iff_small_ext.{w}]
  intro X Y n
  induction n generalizing X Y with
  | zero =>
    rw [small_congr Ext.homEquiv₀]
    infer_instance
  | succ n hn =>
    let S := ShortComplex.mk _ _ (kernel.condition (Projective.π X))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
    have : Function.Surjective (Ext.precomp hS.extClass Y (add_comm 1 n)) := fun x₃ ↦
      Ext.contravariant_sequence_exact₃ hS Y x₃
        (Ext.eq_zero_of_projective _) (by lia)
    exact small_of_surjective.{w} this

