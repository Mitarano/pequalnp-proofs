import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_785

theorem two_mul_card_tri (N : ℕ) :
    2 * Fintype.card (Σ b : Fin N, Fin (b.val + 1)) = N * (N + 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun b => b + 1) N]
  have h := Finset.sum_range_id_mul_two (N + 1)
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.add_sub_cancel, add_zero] at h
  linarith

end PEqualNP.Outside.L_lib_785

open PEqualNP.Outside.L_lib_785 in
theorem PEqualNP.Outside.L_lib_785 : let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (g : ℕ) (D : Fin g → (K →ₗ[F] K)),
  let r := ∑ i, Module.finrank F (LinearMap.range (D i))
  ∃ V : Submodule F K,
    2 * Module.finrank F K ≤ 2 * Module.finrank F V + r*(r+1) ∧
    ∀ w ∈ V, ∀ (S : Finset (Fin g)) (x : K),
      x = w * ∑ i ∈ S, D i x → x = 0 := by
  intro F K _ _ _ g D r
  classical

  let ι := Σ i : Fin g, Fin (Module.finrank F (LinearMap.range (D i)))
  let bas : ∀ i : Fin g, Module.Basis (Fin (Module.finrank F (LinearMap.range (D i)))) F
      (LinearMap.range (D i)) := fun i => Module.finBasis F _
  let u : ι → K := fun a => (bas a.1 a.2 : K)
  let f : ι → (K →ₗ[F] F) := fun a =>
    (Finsupp.lapply a.2) ∘ₗ (bas a.1).repr.toLinearMap ∘ₗ (D a.1).rangeRestrict
  have hdec : ∀ i x, D i x = ∑ j, f ⟨i, j⟩ x • u ⟨i, j⟩ := by
    intro i x
    have h := (bas i).sum_repr ((D i).rangeRestrict x)
    have h' := congrArg (fun y : LinearMap.range (D i) => (y : K)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    rw [show D i x = ((D i).rangeRestrict x : K) from rfl, ← h']
    rfl
  have hcard : Fintype.card ι = r := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fin, r]

  let N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι
  let Q := Σ b : Fin N, Fin (b.val + 1)
  let lo : Q → Fin N := fun q => ⟨q.2.val, lt_of_lt_of_le q.2.isLt (Nat.succ_le_of_lt q.1.isLt)⟩
  let Φ : K →ₗ[F] (Q → F) :=
    LinearMap.pi (fun q => (f (e.symm (lo q))) ∘ₗ LinearMap.mulRight F (u (e.symm q.1)))
  refine ⟨LinearMap.ker Φ, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 : Module.finrank F (LinearMap.range Φ) ≤ Fintype.card Q := by
      have := Submodule.finrank_le (LinearMap.range Φ)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    have h3 : 2 * Fintype.card Q = N * (N + 1) := two_mul_card_tri N
    have h4 : N = r := hcard
    have h5 : N * (N + 1) = r * (r + 1) := by rw [h4]
    omega
  · intro w hw S x hx

    have hkill : ∀ a b : ι, e a ≤ e b → f a (w * u b) = 0 := by
      intro a b hab
      have := congrFun (LinearMap.mem_ker.mp hw) ⟨e b, ⟨(e a).val, Nat.lt_succ_of_le hab⟩⟩
      simp only [Φ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, Pi.zero_apply] at this
      have hlo : e.symm (lo ⟨e b, ⟨(e a).val, Nat.lt_succ_of_le hab⟩⟩) = a := by
        apply e.injective; simp [lo]
      rw [hlo, Equiv.symm_apply_apply] at this
      exact this
    let T : Finset ι := Finset.univ.filter (fun a => a.1 ∈ S)
    have hx2 : x = ∑ b ∈ T, f b x • (w * u b) := by
      have hs : ∑ i ∈ S, D i x = ∑ b ∈ T, f b x • u b := by
        simp only [hdec]
        rw [show T = S.sigma (fun i => (Finset.univ : Finset (Fin (Module.finrank F
            (LinearMap.range (D i)))))) by
          ext a
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => Finset.mem_sigma.mpr ⟨h, Finset.mem_univ _⟩,
            fun h => (Finset.mem_sigma.mp h).1⟩]
        rw [Finset.sum_sigma]
      conv_lhs => rw [hx, hs]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [mul_smul_comm]
    have hzero : ∀ k : ℕ, ∀ a ∈ T, (e a).val = k → f a x = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro a ha hak
        rw [hx2, map_sum]
        refine Finset.sum_eq_zero (fun b hb => ?_)
        rw [map_smul, smul_eq_mul]
        by_cases hab : e a ≤ e b
        · rw [hkill a b hab, mul_zero]
        · have hlt : (e b).val < k := by
            rw [← hak]; exact Fin.lt_def.mp (lt_of_not_ge hab)
          rw [ih _ hlt b hb rfl, zero_mul]
    rw [hx2]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    rw [hzero _ b hb rfl, zero_smul]
