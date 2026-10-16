import E8Leech.CKMRVKernelRectangleBounds

/-! Two overlapping certificates cover a real rectangle, including their shared boundary. -/

namespace E8Leech.Taylor

def leftKernelRectangleBox : Box :=
  ⟨1460 / 10000000000, 1556 / 10000000000,
    3379 / 1000000000, 3599 / 1000000000,
    499 / 100, 501 / 100, 399 / 100, 401 / 100,
    3141592 / 1000000, 3141593 / 1000000, 69 / 100, 7 / 10⟩

def rightKernelRectangleBox : Box :=
  ⟨1414 / 10000000000, 1508 / 10000000000,
    3379 / 1000000000, 3599 / 1000000000,
    5, 251 / 50, 399 / 100, 401 / 100,
    3141592 / 1000000, 3141593 / 1000000, 69 / 100, 7 / 10⟩

def leftKernelRectangle : KernelRectangleCandidate :=
  ⟨leftKernelRectangleBox, 3599 / 1000000000, 1, 3, 2, 2, 4, 10⟩

def rightKernelRectangle : KernelRectangleCandidate :=
  ⟨rightKernelRectangleBox, 3599 / 1000000000, 1, 3, 2, 2, 4, 10⟩

set_option maxHeartbeats 0
set_option maxRecDepth 32768

theorem leftKernelRectangle_checked : checkKernelRectangle leftKernelRectangle = true := by
  decide +kernel

theorem rightKernelRectangle_checked : checkKernelRectangle rightKernelRectangle = true := by
  decide +kernel

theorem leftKernelRectangle_lower_bound_checked :
    checkKernelRectangleLowerBound leftKernelRectangle (1 / 10000000000) = true := by
  simp only [checkKernelRectangleLowerBound, leftKernelRectangle_checked, Bool.true_and]
  decide +kernel

theorem rightKernelRectangle_lower_bound_checked :
    checkKernelRectangleLowerBound rightKernelRectangle (1 / 10000000000) = true := by
  simp only [checkKernelRectangleLowerBound, rightKernelRectangle_checked, Bool.true_and]
  decide +kernel

def adjacentKernelTile : AxisTile := ⟨499 / 100, 251 / 50, 399 / 100, 401 / 100⟩

def adjacentKernelCover : KernelRectangleCover :=
  .splitU 5 (.leaf leftKernelRectangle) (.leaf rightKernelRectangle)

theorem adjacentKernelCover_checked :
    checkKernelRectangleCover adjacentKernelCover adjacentKernelTile = true := by
  simp only [adjacentKernelCover, checkKernelRectangleCover,
    leftKernelRectangle_checked, rightKernelRectangle_checked, Bool.and_true]
  norm_num [AxisTile.CoveredBy, adjacentKernelTile, leftKernelRectangle,
    rightKernelRectangle, leftKernelRectangleBox, rightKernelRectangleBox]

/-- The cover proves the whole enlarged rectangle, without a kernel-sign or regularity premise. -/
theorem ckmrvEightHatKernel_pos_enlarged_rectangle {u t : ℝ}
    (hu : (499 / 100 : ℝ) ≤ u ∧ u ≤ 251 / 50)
    (ht : (399 / 100 : ℝ) ≤ t ∧ t ≤ 401 / 100) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  apply ckmrvEightHatKernel_pos_of_checked_cover adjacentKernelCover adjacentKernelTile
    adjacentKernelCover_checked
  norm_num [AxisTile.Mem, adjacentKernelTile] at hu ht ⊢
  exact ⟨hu.1, hu.2, ht.1, ht.2⟩

/-- The split line itself is included in the certified cover. -/
theorem ckmrvEightHatKernel_pos_cover_split_line {t : ℝ}
    (ht : (399 / 100 : ℝ) ≤ t ∧ t ≤ 401 / 100) :
    0 < (ckmrvEightHatKernel (imagPt 5) (imagPt t)).re :=
  ckmrvEightHatKernel_pos_enlarged_rectangle (by norm_num) ht

/-- An explicit uniform lower bound on the enlarged rectangle. -/
theorem ckmrvEightHatKernel_lower_bound_enlarged_rectangle {u t : ℝ}
    (hu : (499 / 100 : ℝ) ≤ u ∧ u ≤ 251 / 50)
    (ht : (399 / 100 : ℝ) ≤ t ∧ t ≤ 401 / 100) :
    (1 / 10000000000 : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have heps : ((1 / 10000000000 : ℚ) : ℝ) = (1 / 10000000000 : ℝ) := by norm_num
  rw [← heps]
  by_cases h : u ≤ 5
  · apply ckmrvEightHatKernel_lower_bound_of_checked_rectangle leftKernelRectangle_lower_bound_checked
    · norm_num [leftKernelRectangle, leftKernelRectangleBox]
      constructor <;> linarith [hu.1, h]
    · norm_num [leftKernelRectangle, leftKernelRectangleBox] at ht ⊢
      exact ht
  · apply ckmrvEightHatKernel_lower_bound_of_checked_rectangle rightKernelRectangle_lower_bound_checked
    · norm_num [rightKernelRectangle, rightKernelRectangleBox]
      constructor <;> linarith [hu.2, not_le.mp h]
    · norm_num [rightKernelRectangle, rightKernelRectangleBox] at ht ⊢
      exact ht

end E8Leech.Taylor
