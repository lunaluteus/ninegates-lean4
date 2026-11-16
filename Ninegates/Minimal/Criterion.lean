/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Basic
public import Ninegates.Meldable.Elementary
public import Ninegates.Wait.Add

/-! Minimality reduces to forbidding single elementary meld removals. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma IsFullWait.sub_of_decomposition (full : IsFullWait m c) {k : ℕ}
    {remainder removed meld : VirtualHand n} (smaller : IsFullWait k remainder)
    (equal : c = remainder + removed) (remaining : Meldable (removed - meld))
    (count : size meld = 3) : IsFullWait (m - 1) (c - meld) := by
  have positive_m : 0 < m := by have lower := full.meldCount_gt_order; omega
  have shape : c - meld = remainder + (removed - meld) := by rw [equal]; abel
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [shape]
    exact smaller.1.add remaining.nonnegative
  · rw [map_sub, full.2.1, count]
    omega
  · intro i
    obtain ⟨j, edge⟩ := (isFullWait_iff.mp smaller).2.2 i
    rw [shape]
    exact ⟨j, edge.add_meldable remaining⟩

lemma IsFullWait.minimal_of_no_elementary_removal (full : IsFullWait m c)
    (triplets : ∀ i, ¬IsFullWait (m - 1) (c - triplet i))
    (sequences : ∀ r, ¬IsFullWait (m - 1) (c - sequence r)) : IsMinimalFullWait m c := by
  refine ⟨full, ?_⟩
  intro k remainder removed smaller meldable equal
  by_contra nonzero
  rcases meldable.exists_elementary_removal nonzero with ⟨i, remaining⟩ | ⟨r, remaining⟩
  · exact triplets i (full.sub_of_decomposition smaller equal remaining (size_triplet i))
  · exact sequences r (full.sub_of_decomposition smaller equal remaining (size_sequence r))

lemma isMinimalFullWait_iff_no_elementary_removal : IsMinimalFullWait m c ↔
    IsFullWait m c ∧ (∀ i, ¬IsFullWait (m - 1) (c - triplet i)) ∧
      ∀ r, ¬IsFullWait (m - 1) (c - sequence r) := by
  constructor
  · intro minimal
    refine ⟨minimal.full, ?_, ?_⟩
    · intro i smaller
      have empty := minimal.minimal smaller (meldable_triplet i)
        (show c = (c - triplet i) + triplet i by abel)
      have count := congrArg size empty
      simp at count
    · intro r smaller
      have empty := minimal.minimal smaller (meldable_sequence r)
        (show c = (c - sequence r) + sequence r by abel)
      have count := congrArg size empty
      simp at count
  · rintro ⟨full, triplets, sequences⟩
    exact full.minimal_of_no_elementary_removal triplets sequences

end Mahjong.VirtualHand
