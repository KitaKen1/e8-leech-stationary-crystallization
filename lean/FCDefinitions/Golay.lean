import FCDefinitions.E8Coordinates

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def golayBlock : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0;
     1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1;
     1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1;
     1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0;
     1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1;
     1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1;
     1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1;
     1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0;
     1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0;
     1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1]

def golayEncode (a : Fin 12 → ZMod 2) : Fin 24 → ZMod 2 :=
  Fin.append a (a ᵥ* golayBlock)

def golayEncoderLinear : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayEncode
  map_add' a b := by
    ext j
    refine Fin.addCases (m := 12) (n := 12) (fun i => ?_) (fun i => ?_) j
    · simp [golayEncode]
    · simp [golayEncode, add_vecMul, -Fin.natAdd_eq_addNat]
  map_smul' k a := by
    ext j
    refine Fin.addCases (m := 12) (n := 12) (fun i => ?_) (fun i => ?_) j
    · simp [golayEncode]
    · simp [golayEncode, smul_vecMul, -Fin.natAdd_eq_addNat]

def golayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) := LinearMap.range golayEncoderLinear

end E8Leech
