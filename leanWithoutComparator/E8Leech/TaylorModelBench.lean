import E8Leech.TaylorModelOps

/-!
# Kernel speed check for the Taylor-model arithmetic (not part of the main development)

The third check of this file, `mul2_len` (the product of the product with itself, about 1.7·10⁵
monomial products), was moved to `research/benchmarks/TaylorModelBenchHeavy.lean` on 2026-10-15: its
kernel check needs more than 7 GB of memory, so the library could not be built within the memory
limit of the clean build. The two checks here need about 2 GB.
-/

set_option profiler true
set_option profiler.threshold 200

namespace E8Leech.Taylor.Bench

def amono (n : ℕ) : Mono := ⟨n, 0, 0, 0, 0, 0⟩
def bmono (n : ℕ) : Mono := ⟨0, n, 0, 0, 0, 0⟩

/-- A dense polynomial `Σ_{i+j ≤ 9} (i+1)/(j+1) aⁱ bʲ` with 55 terms. -/
def dense9 : Poly :=
  (List.range 10).flatMap fun i => (List.range (10 - i)).map fun j =>
    (⟨i, j, 0, 0, 0, 0⟩, ((i + 1 : ℕ) : ℚ) / ((j + 1 : ℕ) : ℚ))

def box0 : Box := ⟨0, 1 / 23, 0, 1 / 23, 1, 2, 1, 2, 3, 4, 1 / 2, 1⟩

/-- Pure polynomial product, 55 × 55 = 3025 monomial products. -/
theorem mul_len : (Poly.mul dense9 dense9).length ≤ 400 := by decide +kernel

/-- Bound of the product (3025 terms before merging). -/
theorem bound_small : Poly.bound box0 (Poly.mul dense9 dense9) < 10 := by decide +kernel

end E8Leech.Taylor.Bench
