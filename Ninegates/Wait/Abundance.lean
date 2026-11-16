/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Coverage
public import Ninegates.Meldable.Virtual
public import Ninegates.Meldable.OrderOne
public import Ninegates.Wait.Basic
public import Ninegates.Hand.Classes

/-! Above the threshold hand, every congruence-permitted draw-pair edge exists. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma virtuallyMeldable_draw_iff (count : (size c : ZMod 3) = 1) (i j : Rank n) :
    VirtuallyMeldable (c + single i - pair j) ↔
      rankClass i + rankClass j = -(rankSum c : ZMod 3) := by
  rw [virtuallyMeldable_iff_size_rankSum]
  simp only [map_sub, map_add, size_single, size_pair, rankSum_single, rankSum_pair]
  push_cast
  rw [count]
  change (1 + 1 - 2 = (0 : ZMod 3) ∧
    (rankSum c : ZMod 3) + rankClass i - 2 * rankClass j = 0) ↔ _
  · have three : (3 : ZMod 3) * rankClass j = 0 := by
      rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
    constructor
    · rintro ⟨_, weighted⟩
      linear_combination weighted + three
    · intro congruent
      refine ⟨by norm_num, ?_⟩
      linear_combination congruent - three

lemma drawPair_of_abundant (count : (size c : ZMod 3) = 1)
    (large : abundanceThreshold ≤ c) (i j : Rank n)
    (congruent : rankClass i + rankClass j = -(rankSum c : ZMod 3)) : DrawPair c i j := by
  apply ((virtuallyMeldable_draw_iff count i j).mpr congruent).meldable_of_ge_threshold
  intro k
  have floor : abundanceThreshold k ≤ c k := large k
  have nonnegative : 0 ≤ single i k := nonnegative_single i k
  have pair_bound : pair j k ≤ 2 := by
    simp only [pair_apply, single_apply]
    split_ifs <;> norm_num
  change abundanceThreshold k - 2 ≤ c k + single i k - pair j k
  linarith

lemma isFullWait_of_abundant (order : 0 < n) (large : abundanceThreshold ≤ c)
    (count : size c = 3 * (m : ℤ) + 1) : IsFullWait m c := by
  have residue : (size c : ZMod 3) = 1 := by
    rw [count]
    push_cast
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
  apply isFullWait_iff.mpr
  refine ⟨?_, count, ?_⟩
  · intro i
    change 0 ≤ c i
    have floor : abundanceThreshold i ≤ c i := large i
    have lower := (abundanceThreshold_bounds i).1
    linarith
  · intro i
    obtain ⟨j, class_j⟩ := exists_rankClass order (-(rankSum c : ZMod 3) - rankClass i)
    exact ⟨j, drawPair_of_abundant residue large i j (by rw [class_j]; ring)⟩

/-- At order one, two copies at each rank suffice for every permitted edge. -/
lemma drawPair_orderOne_of_two {c : VirtualHand 1} (count : (size c : ZMod 3) = 1)
    (large : ∀ i, 2 ≤ c i) (i j : Rank 1)
    (congruent : rankClass i + rankClass j = -(rankSum c : ZMod 3)) : DrawPair c i j := by
  apply ((virtuallyMeldable_draw_iff count i j).mpr congruent).meldable_orderOne
  intro k
  change 0 ≤ c k + single i k - pair j k
  have lower := large k
  have single_positive : 0 ≤ single i k := nonnegative_single i k
  have pair_bound : pair j k ≤ 2 := by
    simp only [pair_apply, single_apply]
    split_ifs <;> norm_num
  linarith

lemma isFullWait_orderOne_of_two {c : VirtualHand 1} (large : ∀ i, 2 ≤ c i)
    (count : size c = 3 * (m : ℤ) + 1) : IsFullWait m c := by
  have residue : (size c : ZMod 3) = 1 := by
    rw [count]
    push_cast
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
  apply isFullWait_iff.mpr
  refine ⟨?_, count, ?_⟩
  · intro i
    change 0 ≤ c i
    exact le_trans (by norm_num) (large i)
  · intro i
    obtain ⟨j, class_j⟩ := exists_rankClass (n := 1) (by decide)
      (-(rankSum c : ZMod 3) - rankClass i)
    exact ⟨j, drawPair_orderOne_of_two residue large i j (by rw [class_j]; ring)⟩

end Mahjong.VirtualHand
