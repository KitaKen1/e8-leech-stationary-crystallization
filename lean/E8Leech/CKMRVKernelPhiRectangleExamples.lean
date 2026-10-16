import E8Leech.CKMRVKernelPhiRectangles
import E8Leech.CKMRVKernelRectangleExamples

/-! Concrete closed covers for the numerator-only and common-lower-bound checkers. -/

namespace E8Leech.Taylor

set_option maxHeartbeats 0
set_option maxRecDepth 32768

theorem leftKernelPhiRectangle_checked : checkKernelPhiRectangle leftKernelRectangle = true := by
  apply checkKernelPhiRectangle_eq_true_of_full leftKernelRectangle_checked
  norm_num [leftKernelRectangle, leftKernelRectangleBox]

theorem rightKernelPhiRectangle_checked : checkKernelPhiRectangle rightKernelRectangle = true := by
  apply checkKernelPhiRectangle_eq_true_of_full rightKernelRectangle_checked
  norm_num [rightKernelRectangle, rightKernelRectangleBox]

theorem adjacentKernelPhiCover_checked :
    checkKernelPhiRectangleCover adjacentKernelCover adjacentKernelTile = true := by
  simp only [checkKernelPhiRectangleCover, adjacentKernelCover, checkKernelRectangleCoverWith,
    leftKernelPhiRectangle_checked, rightKernelPhiRectangle_checked, Bool.and_true]
  norm_num [AxisTile.CoveredBy, adjacentKernelTile, leftKernelRectangle,
    rightKernelRectangle, leftKernelRectangleBox, rightKernelRectangleBox]

theorem adjacentKernelLowerBoundCover_checked :
    checkKernelRectangleLowerBoundCover (1 / 10000000000)
      adjacentKernelCover adjacentKernelTile = true := by
  simp only [checkKernelRectangleLowerBoundCover, adjacentKernelCover,
    checkKernelRectangleCoverWith, leftKernelRectangle_lower_bound_checked,
    rightKernelRectangle_lower_bound_checked, Bool.and_true]
  norm_num [AxisTile.CoveredBy, adjacentKernelTile, leftKernelRectangle,
    rightKernelRectangle, leftKernelRectangleBox, rightKernelRectangleBox]

/-- A uniform bound obtained by the generic cover theorem, with no manual split in this proof. -/
theorem ckmrvEightHatKernel_lower_bound_enlarged_rectangle_via_cover {u t : ℝ}
    (hu : (499 / 100 : ℝ) ≤ u ∧ u ≤ 251 / 50)
    (ht : (399 / 100 : ℝ) ≤ t ∧ t ≤ 401 / 100) :
    (1 / 10000000000 : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hm : adjacentKernelTile.Mem u t := by
    norm_num [AxisTile.Mem, adjacentKernelTile] at hu ht ⊢
    exact ⟨hu.1, hu.2, ht.1, ht.2⟩
  have h := ckmrvEightHatKernel_lower_bound_of_checked_cover _ _
    adjacentKernelLowerBoundCover_checked hm
  norm_num at h ⊢
  exact h

def diagonalKernelPhiRectangleBox : Box :=
  ⟨17431 / 5000000000, 6977 / 2000000000,
    17431 / 5000000000, 6977 / 2000000000,
    39999 / 10000, 40001 / 10000, 39999 / 10000, 40001 / 10000,
    3141592 / 1000000, 3141593 / 1000000, 69 / 100, 7 / 10⟩

def diagonalKernelPhiRectangle : KernelRectangleCandidate :=
  ⟨diagonalKernelPhiRectangleBox, 6977 / 2000000000, 1, 3, 2, 2, 4, 10⟩

/-- The real endpoint and numerator checks succeed even though this rectangle meets u = t. -/
theorem diagonalKernelPhiRectangle_checked :
    checkKernelPhiRectangle diagonalKernelPhiRectangle = true := by
  decide +kernel

def diagonalKernelPhiTile : AxisTile :=
  ⟨39999 / 10000, 40001 / 10000, 39999 / 10000, 40001 / 10000⟩

def diagonalKernelPhiCover : KernelRectangleCover :=
  .splitU 4
    (.splitT 4 (.leaf diagonalKernelPhiRectangle) (.leaf diagonalKernelPhiRectangle))
    (.splitT 4 (.leaf diagonalKernelPhiRectangle) (.leaf diagonalKernelPhiRectangle))

/-- Both split directions are checked; all four children share the certified source box. -/
theorem diagonalKernelPhiCover_checked :
    checkKernelPhiRectangleCover diagonalKernelPhiCover diagonalKernelPhiTile = true := by
  simp only [checkKernelPhiRectangleCover, diagonalKernelPhiCover,
    checkKernelRectangleCoverWith, diagonalKernelPhiRectangle_checked, Bool.and_true]
  norm_num [AxisTile.CoveredBy, diagonalKernelPhiTile, diagonalKernelPhiRectangle,
    diagonalKernelPhiRectangleBox]

theorem ckmrvEightHatKernel_nonneg_diagonal_rectangle {u t : ℝ}
    (hu : (39999 / 10000 : ℝ) ≤ u ∧ u ≤ 40001 / 10000)
    (ht : (39999 / 10000 : ℝ) ≤ t ∧ t ≤ 40001 / 10000) :
    0 ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  apply ckmrvEightHatKernel_nonneg_of_checked_phi_cover _ _ diagonalKernelPhiCover_checked
  norm_num [AxisTile.Mem, diagonalKernelPhiTile] at hu ht ⊢
  exact ⟨hu.1, hu.2, ht.1, ht.2⟩

theorem ckmrvEightHatKernel_pos_diagonal_rectangle_regular {u t : ℝ}
    (hu : (39999 / 10000 : ℝ) ≤ u ∧ u ≤ 40001 / 10000)
    (ht : (39999 / 10000 : ℝ) ≤ t ∧ t ≤ 40001 / 10000) (hut : u ≠ t) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  apply ckmrvEightHatKernel_pos_of_checked_phi_cover _ _ diagonalKernelPhiCover_checked _ hut
  norm_num [AxisTile.Mem, diagonalKernelPhiTile] at hu ht ⊢
  exact ⟨hu.1, hu.2, ht.1, ht.2⟩

end E8Leech.Taylor
