/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.V3.Hand.Size

/-! Counting alternating coordinates on the `3n` ranks. -/

@[expose] public section

namespace Mahjong.V3.VirtualHand

def parityMatch (n : ℕ) : VirtualHand n := fun i ↦ if (i.val + n) % 2 = 0 then 1 else 0

@[grind =]
lemma parityMatch_apply {n : ℕ} (i : Rank n) :
    parityMatch n i = if (i.val + n) % 2 = 0 then 1 else 0 := rfl

lemma size_parityMatch (n : ℕ) : size (parityMatch n) = (3 * n / 2 : ℕ) := by
  let index (t : Fin (3 * n / 2)) : Rank n := ⟨2 * t.val + n % 2, by have := t.isLt; omega⟩
  have injective : Function.Injective index := by
    intro a b equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    dsimp [index] at values
    omega
  have indices : Finset.univ.filter (fun i : Rank n ↦ (i.val + n) % 2 = 0) =
      Finset.univ.image index := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro member
      refine ⟨⟨i.val / 2, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      dsimp only [index]
      omega
    · rintro ⟨t, rfl⟩
      dsimp only [index]
      omega
  change (∑ i : Rank n, if (i.val + n) % 2 = 0 then (1 : ℤ) else 0) = _
  rw [← Finset.sum_filter, indices]
  simp [Finset.card_image_of_injective _ injective]

end Mahjong.V3.VirtualHand
