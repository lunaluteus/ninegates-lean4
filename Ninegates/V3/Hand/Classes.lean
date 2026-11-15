/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.V3.Hand.Basic

/-!
# Ranks grouped by congruence class

The product coordinates are a block number and a zero-based position in that
block. Paper congruence classes `1,2,0` correspond to positions `0,1,2`.
-/

@[expose] public section

namespace Mahjong.V3.VirtualHand

variable {n : ℕ}

def blockEquiv (n : ℕ) : Fin n × Fin 3 ≃ Rank n :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 3))

@[simp, grind =]
lemma blockEquiv_val (b : Fin n) (r : Fin 3) : (blockEquiv n (b, r)).val = 3 * b.val + r.val := by
  change r.val + 3 * b.val = 3 * b.val + r.val
  omega

@[simp]
lemma rankClass_blockEquiv (b : Fin n) (r : Fin 3) :
    rankClass (blockEquiv n (b, r)) = (r.val : ZMod 3)+1 := by
  unfold rankClass rank
  rw [blockEquiv_val]
  push_cast
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]
  ring

lemma classSize_blocks (c : VirtualHand n) (r : Fin 3) :
    classSize ((r.val : ZMod 3)+1) c = ∑ b : Fin n, c (blockEquiv n (b, r)) := by
  have equal (j : Fin 3) : ((j.val : ZMod 3)+1 = (r.val : ZMod 3)+1) ↔ j = r := by
    simp [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt,
      Nat.mod_eq_of_lt r.isLt, Fin.ext_iff]
  simp only [classSize, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_filter]
  rw [← (blockEquiv n).sum_comp]
  simp only [Fintype.sum_prod_type, rankClass_blockEquiv, equal]
  simp

lemma classSize_one_blocks (c : VirtualHand n) :
    classSize 1 c = ∑ b : Fin n, c (blockEquiv n (b, 0)) := by
  simpa using classSize_blocks c 0

lemma classSize_two_blocks (c : VirtualHand n) :
    classSize 2 c = ∑ b : Fin n, c (blockEquiv n (b, 1)) := by
  simpa [show (1 : ZMod 3)+1 = 2 by decide +kernel] using classSize_blocks c 1

lemma classSize_zero_blocks (c : VirtualHand n) :
    classSize 0 c = ∑ b : Fin n, c (blockEquiv n (b, 2)) := by
  simpa [show (2 : ZMod 3)+1 = 0 by decide +kernel] using classSize_blocks c 2

end Mahjong.V3.VirtualHand
