import Mathlib

section

variable {A B F : Type*} [Semiring A] [Semiring B]

theorem IsLocalHom.isField [FunLike F A B] [MonoidWithZeroHomClass F A B] {f : F}
    [IsLocalHom f] (inj : Function.Injective f) (hB : IsField B) : IsField A where
  exists_pair_ne := have : Nontrivial B := ⟨hB.1⟩; (domain_nontrivial f (map_zero f) (map_one f)).1
  mul_comm x y := inj <| by rw [map_mul, map_mul, hB.mul_comm]
  mul_inv_cancel h :=
    have ⟨a', he⟩ := hB.mul_inv_cancel ((inj.ne h).trans_eq <| map_zero f)
    let _ := hB.toSemifield
    (IsUnit.of_mul_eq_one _ he).of_map.exists_right_inv

end
