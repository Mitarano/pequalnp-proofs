import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21585
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [0, 10]⟩], 11⟩
end PEqualNP.Outside.L_meta_21585

open PEqualNP.Outside.L_meta_21585 in
theorem PEqualNP.Outside.L_meta_21585 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266335 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
