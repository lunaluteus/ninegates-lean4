/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Classes

/-! At order one every congruence class consists of exactly one rank. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma classSize_orderOne (c : VirtualHand 1) (i : Rank 1) : classSize (rankClass i) c = c i := by
  apply classSize_eq_single i
  intro j same different
  have residue := (rankClass_eq_iff j i).mp same
  have bound_i := i.isLt
  have bound_j := j.isLt
  have equal : j = i := Fin.ext (by omega)
  exact (different equal).elim

end Mahjong.VirtualHand
