/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.V3.Hand.Defs

/-! Elementary patterns and linear tile statistics for virtual hands. -/

@[expose] public section

namespace Mahjong.V3.VirtualHand

variable {n : ℕ}

@[simp, grind =]
lemma nonnegative_iff (c : VirtualHand n) : Nonnegative c ↔ ∀ i, 0 ≤ c i := Iff.rfl

@[simp, grind =]
lemma bounded_iff (cap : ℕ) (c : VirtualHand n) :
    Bounded cap c ↔ (∀ i, 0 ≤ c i) ∧ ∀ i, c i ≤ cap := Iff.rfl

@[simp, grind =]
lemma valid_iff (c : VirtualHand n) : Valid c ↔ Bounded 4 c := Iff.rfl

@[grind =]
lemma single_apply (i j : Rank n) : single i j = if j = i then 1 else 0 := rfl

@[simp]
lemma single_self (i : Rank n) : single i i = 1 := by simp [single]

@[simp]
lemma single_of_ne {i j : Rank n} (h : j ≠ i) : single i j = 0 := by simp [single, h]

@[simp, grind =]
lemma pair_apply (i j : Rank n) : pair i j = 2 * single i j := rfl

@[simp, grind =]
lemma triplet_apply (i j : Rank n) : triplet i j = 3 * single i j := rfl

@[simp, grind =]
lemma reverse_apply (c : VirtualHand n) (i : Rank n) : reverse c i = c i.rev := rfl

@[simp, grind =]
lemma reverse_reverse (c : VirtualHand n) : reverse (reverse c) = c := by ext; simp

@[simp]
lemma nonnegative_single (i : Rank n) : Nonnegative (single i) := by
  intro j
  simp only [single]
  split <;> norm_num

@[simp]
lemma nonnegative_zero : Nonnegative (0 : VirtualHand n) := le_refl _

lemma Nonnegative.add {c d : VirtualHand n} (hc : Nonnegative c) (hd : Nonnegative d) :
    Nonnegative (c + d) := add_nonneg hc hd

@[simp]
lemma size_single (i : Rank n) : size (single i) = 1 := by simp [size, single]

@[simp]
lemma size_pair (i : Rank n) : size (pair i) = 2 := by rw [pair, map_smul]; simp

@[simp]
lemma size_triplet (i : Rank n) : size (triplet i) = 3 := by rw [triplet, map_smul]; simp

@[simp]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by simp [sequence]

@[simp]
lemma rankSum_single (i : Rank n) : rankSum (single i) = rank i := by
  simp [rankSum, single]

@[simp]
lemma rankSum_pair (i : Rank n) : rankSum (pair i) = 2 * rank i := by rw [pair, map_smul]; simp

@[simp]
lemma rankSum_triplet (i : Rank n) : rankSum (triplet i) = 3 * rank i := by
  rw [triplet, map_smul]; simp

@[simp]
lemma rankSum_sequence (i : Fin (3 * n - 2)) : rankSum (sequence i) = 3 * (i.val + 2) := by
  simp [sequence, rank]
  ring

@[grind =]
lemma classSize_single (r : ZMod 3) (i : Rank n) :
    classSize r (single i) = if rankClass i = r then 1 else 0 := by
  simp [classSize, single]

/-- Proposition `prp-class-size-sum-congruence`, the class-size partition. -/
lemma size_eq_sum_classSize (c : VirtualHand n) : size c = ∑ r : ZMod 3, classSize r c := by
  simp only [classSize, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [size]

/-- The rank sum modulo three is determined by the three class sizes. -/
lemma rankSum_cast (c : VirtualHand n) :
    (rankSum c : ZMod 3) = ∑ r : ZMod 3, r * (classSize r c : ZMod 3) := by
  calc
    _ = ∑ i, rankClass i * (c i : ZMod 3) := by simp [rankSum, rankClass]
    _ = ∑ i : Rank n, ∑ r : ZMod 3,
        if rankClass i = r then r * (c i : ZMod 3) else 0 := by simp
    _ = ∑ r : ZMod 3, ∑ i : Rank n,
        if rankClass i = r then r * (c i : ZMod 3) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      simp [classSize, Finset.sum_filter, Finset.mul_sum, mul_ite]

end Mahjong.V3.VirtualHand
