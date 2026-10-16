/- Explicit `ψI` numerator coefficient table (`ℤ`, length `100`). -/
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.PsiInumCoeffsTable

/-!
### `ψI` numerator coefficients (as integers)

The explicit coefficient table lives in `Dim24.Inequalities.AppendixA.PsiInumCoeffsTable`.
Here we provide the simp lemma connecting `BleadingCoeffs.psiInumCoeffs` to the table.
-/

namespace SpherePacking.Dim24.AppendixA

set_option maxHeartbeats 1000000 in
-- The `decide` certificate below is expensive.
set_option maxRecDepth 4000 in
-- Needed to avoid recursion-depth timeouts.
private lemma psiInumCoeffs_table_eq : BleadingCoeffs.psiInumCoeffs = psiInumCoeffs_table := by
  -- One kernel computation; kept in a dedicated file to isolate the cost.
  decide

/-- `getD` access to `BleadingCoeffs.psiInumCoeffs` agrees with the explicit table. -/
@[simp] public lemma psiInumCoeffs_getD_eq (n : ℕ) :
    BleadingCoeffs.psiInumCoeffs.getD n 0 = psiInumCoeffs_table.getD n 0 := by
  simp [psiInumCoeffs_table_eq]

end SpherePacking.Dim24.AppendixA
