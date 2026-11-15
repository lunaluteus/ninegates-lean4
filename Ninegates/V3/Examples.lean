/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.V3.Wait.Basic

/-!
# A full wait beyond the old fixed meld count

The paper's `(0, 2, 2, 4, 2, 3)` is a full-sided `(2, 4)`-wait. Explicit meld
placements verify each draw, without a decision procedure for meldability.
The same hand is live with five copies, but not with four copies.
-/

@[expose] public section

namespace Mahjong.V3.Examples

open VirtualHand

def largeHand : VirtualHand 2 := ![0, 2, 2, 4, 2, 3]

private def eye : Rank 2 → Rank 2 := ![4, 3, 5, 1, 3, 5]
private def sequences : Rank 2 → Fin 4 → ℤ :=
  ![![1, 1, 0, 0], ![0, 0, 2, 0], ![0, 2, 1, 1],
    ![0, 0, 2, 0], ![0, 2, 0, 0], ![0, 2, 0, 2]]
private def triplets : Rank 2 → Rank 2 → ℤ :=
  ![![0, 0, 0, 1, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0]]

private lemma drawPair (i : Rank 2) : DrawPair largeHand i (eye i) := by
  refine ⟨⟨sequences i, triplets i⟩, ?_, ?_⟩
  · constructor <;> intro j <;> fin_cases i <;> fin_cases j <;>
      norm_num [sequences, triplets]
  · ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [Placement.toHand, sequences, triplets, VirtualHand.sequence, triplet, pair,
        VirtualHand.single, largeHand, eye, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]

lemma largeHand_isFullWait : IsFullWait 4 largeHand := by
  rw [isFullWait_iff]
  refine ⟨?_, ?_, fun i ↦ ⟨eye i, drawPair i⟩⟩
  · intro i
    fin_cases i <;> norm_num [largeHand]
  · norm_num [size, largeHand, Fin.sum_univ_succ]

lemma largeHand_not_live_four : ¬IsLiveFullWait 4 4 largeHand := by
  intro live
  have bound := (isLiveFullWait_iff.mp live).2 (3 : Rank 2)
  norm_num [largeHand] at bound

lemma largeHand_live_five : IsLiveFullWait 5 4 largeHand := by
  rw [isLiveFullWait_iff]
  refine ⟨largeHand_isFullWait, ?_⟩
  intro i
  fin_cases i <;> norm_num [largeHand]

end Mahjong.V3.Examples
