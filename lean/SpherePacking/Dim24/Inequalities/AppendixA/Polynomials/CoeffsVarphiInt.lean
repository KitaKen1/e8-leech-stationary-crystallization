module
import Mathlib.Init
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Rat.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsVarphi


/-!
# Integer coefficient list for `varphi_trunc_geOne`

This file provides the same coefficient list as `AppendixA.varphi_trunc_geOne_coeffs`, but as a
list of integers. It is used by certificate computations that operate in `ℤ` and then cast back to
`ℚ`.
-/

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The coefficients of `varphi_trunc_geOne`, but in `ℤ`. -/
@[expose]
public abbrev varphi_trunc_geOne_coeffsZV : List ℤ :=
  [
    0, 0, 0,
    -3657830400,
    -138997555200,
    -2567796940800,
    -27477621964800,
    -203324160614400,
    -1155903669043200,
    -5339174090342400,
    -21015084264652800,
    -72521005100544000,
    -224861553797529600,
    -636227181370368000,
    -1668067755850137600,
    -4088240185030041600,
    -9465006273911193600,
    -20805434866660147200,
    -43762572956919398400,
    -88336945205133004800,
    -172165667853905510400,
    -324488143313303961600,
    -594362510499631104000,
    -1058782723045692825600,
    -1842067990617794150400,
    -3130150325265911808000,
    -5214476797983852134400,
    -8512870940663517388800,
    -13665057313532741222400,
    -21553564720975941427200,
    -33507016825359251865600,
    -51291681844702924800000,
    -77536607016237465600000,
    -115618862124723518668800,
    -170522966849069540966400,
    -248444586925890995404800,
    -358502398070580823449600,
    -511643460127814809804800,
    -724008584692749171916800,
    -1014348752611232261529600,
    -1410382780836430012416000,
    -1943278742343110086656000,
    -2659501441752744237465600,
    -3609399073079654501068800,
    -4869023515423164208742400,
    -6517936319058852697497600,
    -8677783014902068322304000,
    -11471419168439199027609600,
    -15090221607393063901593600,
    -19719414169554146181120000
  ]

/-- `varphi_trunc_geOne_coeffs` is the `ℚ`-cast of `varphi_trunc_geOne_coeffsZV`. -/
public theorem varphi_trunc_geOne_coeffs_eq_map :
    varphi_trunc_geOne_coeffs = List.map (fun z : ℤ => (z : ℚ)) varphi_trunc_geOne_coeffsZV := by
  simp [varphi_trunc_geOne_coeffs, varphi_trunc_geOne_coeffsZV]

end

end SpherePacking.Dim24.AppendixA
