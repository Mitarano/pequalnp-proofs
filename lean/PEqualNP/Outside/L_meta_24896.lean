import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24896
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [2, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [0, 12]⟩], 13⟩
end PEqualNP.Outside.L_meta_24896

open PEqualNP.Outside.L_meta_24896 in
theorem PEqualNP.Outside.L_meta_24896 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2297407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
