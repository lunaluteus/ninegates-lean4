/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Graph

/-! The class-size congruence for hands of size one modulo three. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

/-- `prp-class-size-congruence`: every nonfixed class has one fewer tile modulo
three than the fixed class. This needs only the size congruence, not waiting. -/
lemma classSize_nonfixed_congruence {c : VirtualHand n} (count : (size c : ZMod 3) = 1)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
    (classSize r c : ZMod 3) + 1 = (classSize (fixedClass c) c : ZMod 3) := by
  have positive : 0 < n := by
    by_contra not_positive
    have zero : n = 0 := by omega
    subst n
    simp [size] at count
  obtain ⟨i, class_i⟩ := exists_rankClass positive (fixedClass c)
  have virtual : VirtuallyMeldable (c - single i) := by
    apply (virtuallyMeldable_iff_size_rankSum _).mpr
    constructor
    · simp only [map_sub, size_single, Int.cast_sub, Int.cast_one, count, sub_self]
    · simp only [map_sub, rankSum_single, Int.cast_sub]
      change fixedClass c - rankClass i = 0
      rw [class_i, sub_self]
  have same := virtual.classSize_cast_eq r (fixedClass c)
  simp only [map_sub, classSize_single, class_i, ite_eq_right nonfixed.symm] at same
  push_cast at same
  linear_combination same

end Mahjong.VirtualHand
