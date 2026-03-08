/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.LogExp
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x q r : ℝ}

/-! # Matrix powers with real exponents

-/

noncomputable section
namespace HermitianMat

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (A : HermitianMat d 𝕜) (r : ℝ) : HermitianMat d 𝕜 :=
  A.cfc (Real.rpow · r)

instance instRPow : Pow (HermitianMat d 𝕜) ℝ :=
  ⟨rpow⟩

theorem rpow_conj_unitary (A : HermitianMat d 𝕜) (U : Matrix.unitaryGroup d 𝕜) (r : ℝ) :
    (HermitianMat.conj U.val A) ^ r = HermitianMat.conj U.val (A ^ r) := by
  exact A.cfc_conj_unitary (· ^ r) U

theorem pow_eq_rpow : A ^ r = A.rpow r :=
  rfl

theorem rpow_eq_cfc : A ^ r = A.cfc (· ^ r) :=
  rfl

theorem diagonal_pow (f : d → ℝ) :
    (diagonal 𝕜 f) ^ r = diagonal 𝕜 (fun i ↦ (f i) ^ r) := by
  simp [rpow_eq_cfc]
  rfl

@[fun_prop]
theorem rpow_const_continuous {r : ℝ} (hr : 0 ≤ r) : Continuous (fun A : HermitianMat d ℂ ↦ A ^ r) := by
  exact HermitianMat.cfc_continuous (Real.continuous_rpow_const hr)

@[fun_prop]
theorem const_rpow_continuous [NonSingular A] : Continuous (fun r : ℝ ↦ A ^ r) := by
  rw [← continuousOn_univ]
  apply continuousOn_cfc_fun_nonsingular
  simp only [Real.rpow_eq_pow]
  fun_prop (disch := assumption)

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x > 0.
-/
@[fun_prop]
theorem continuousOn_rpow_pos (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Ioi 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne').continuousWithinAt

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
@[fun_prop]
theorem continuousOn_rpow_neg (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Iio 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne).continuousWithinAt

@[simp]
theorem rpow_one : A ^ (1 : ℝ) = A := by
  simp [rpow_eq_cfc]

/--
Functional calculus of Real.sqrt is equal to functional calculus of x^(1/2).
-/
lemma sqrt_eq_cfc_rpow_half (A : HermitianMat d 𝕜)  :
    A.sqrt = A.cfc (fun x ↦ x ^ (1/2 : ℝ)) := by
  rw [sqrt, cfc_eq_cfc_iff_eqOn]
  intro
  simp [Real.sqrt_eq_rpow]

@[simp]
theorem one_rpow : (1 : HermitianMat d 𝕜) ^ r = 1 := by
  rcases isEmpty_or_nonempty d
  · apply Subsingleton.allEq
  · nth_rw 2 [← HermitianMat.cfc_id (1 : HermitianMat d 𝕜)]
    rw [rpow_eq_cfc]
    gcongr
    simp

/-- Keeps in line with our simp-normal form for moving reindex outwards. -/
@[simp]
theorem reindex_rpow (e : d ≃ d₂) :
    A.reindex e ^ r = (A ^ r).reindex e := by
  apply A.cfc_reindex

theorem mat_rpow_add (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).mat = (A ^ p).mat * (A ^ q).mat := by
  simp only [rpow_eq_cfc, ← mat_cfc_mul, ← HermitianMat.ext_iff]
  exact cfc_congr_of_nonneg hA (fun i hi ↦ Real.rpow_add' hi hpq)

theorem rpow_mul (hA : 0 ≤ A) {p q : ℝ} : A ^ (p * q) = (A ^ p) ^ q := by
  simp only [rpow_eq_cfc, ← cfc_comp]
  exact cfc_congr_of_nonneg hA (fun i hi ↦ Real.rpow_mul hi p q)

theorem conj_rpow (hA : 0 ≤ A) (hq : q ≠ 0) (hqr : r + 2 * q ≠ 0) :
    (A ^ r).conj (A ^ q) = A ^ (r + 2 * q) := by
  simp only [rpow_eq_cfc, cfc_conj]
  refine cfc_congr_of_nonneg hA (fun i hi ↦ ?_)
  rw [pow_two, Real.rpow_add' hi hqr, two_mul, Real.rpow_add' hi (by simpa)]
  rfl

theorem pow_half_mul (hA : 0 ≤ A) :
    (A ^ (1/2 : ℝ)).mat * (A ^ (1/2 : ℝ)).mat = A := by
  rw [← mat_rpow_add hA]
  · norm_num
  · norm_num

theorem rpow_pos {A : HermitianMat d 𝕜} (hA : 0 < A) {p : ℝ} : 0 < A ^ p := by
  convert cfc_pos_of_pos hA _ _
  · exact fun i hi => Real.rpow_pos_of_pos hi _
  · rcases eq_or_ne p 0 with h | h <;> simp [h]

theorem rpow_nonneg (hA : 0 ≤ A) {p : ℝ} : 0 ≤ A ^ p := by
  apply cfc_nonneg_of_nonneg hA
  exact fun i hi => Real.rpow_nonneg hi p

open ComplexOrder in
theorem inv_eq_rpow_neg_one (hA : A.mat.PosDef) : A⁻¹ = A ^ (-1 : ℝ) := by
  have := nonSingular_of_posDef hA
  rw [← cfc_inv, rpow_eq_cfc]
  simp_rw [Real.rpow_neg_one]

open ComplexOrder in
theorem sandwich_self (hB : B.mat.PosDef) :
    (B.conj (B ^ (-1/2 : ℝ)).mat) = 1 := by
  have hB_inv_sqrt : (B ^ (-1 / 2 : ℝ)).mat * (B ^ (-1 / 2 : ℝ)).mat = (B ^ (-1 : ℝ)).mat := by
    rw [ ← mat_rpow_add ] <;> norm_num
    rw [zero_le_iff]
    exact hB.posSemidef
  have hB_inv : (B ^ (-1 : ℝ)).mat = B.mat⁻¹ := by
    rw [← inv_eq_rpow_neg_one hB, mat_inv]
  rw [ hB_inv ] at hB_inv_sqrt;
  ext1
  simp [mul_assoc];
  rw [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp ];
  rw [ ← Matrix.mul_assoc, hB_inv_sqrt, Matrix.nonsing_inv_mul _ ];
  exact isUnit_iff_ne_zero.mpr hB.det_pos.ne'

open ComplexOrder in
lemma rpow_inv_eq_neg_rpow (hA : A.mat.PosDef) (p : ℝ) : (A ^ p)⁻¹ = A ^ (-p) := by
  --TODO cleanup
  ext i j;
  have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
    have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
      have h_pow : (A ^ p).mat = A.cfc (fun x => x ^ p) := by
        exact rfl
      have h_pow_neg : (A ^ (-p)).mat = A.cfc (fun x => x ^ (-p)) := by
        exact rfl
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = A.cfc (fun x => x ^ p * x ^ (-p)) := by
        rw [ h_pow, h_pow_neg, ← mat_cfc_mul ];
        rfl;
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = A.cfc (fun x => 1) := by
        rw [ h_inv ];
        refine' congr_arg _ ( cfc_congr_of_posDef hA _ );
        exact fun x hx => by simp [ ← Real.rpow_add hx ] ;
      rw [ h_inv, cfc_const ] ; norm_num;
    exact h_inv;
  -- By definition of matrix inverse, if $(A^p) * (A^{-p}) = 1$, then $(A^{-p})$ is the inverse of $(A^p)$.
  have h_inv_def : (A ^ p).mat⁻¹ = (A ^ (-p)).mat := by
    exact Matrix.inv_eq_right_inv h_inv;
  convert congr_fun ( congr_fun h_inv_def i ) j using 1

open ComplexOrder in
lemma sandwich_le_one (hB : B.mat.PosDef) (h : A ≤ B) :
    (A.conj (B ^ (-1/2 : ℝ)).mat) ≤ 1 := by
  convert ← conj_mono h using 1
  exact sandwich_self hB

open ComplexOrder in
lemma rpow_neg_mul_rpow_self (hA : A.mat.PosDef) (p : ℝ) :
    (A ^ (-p)).mat * (A ^ p).mat = 1 := by
  have := rpow_inv_eq_neg_rpow hA p;
  rw [ ← this ];
  -- Since $A$ is positive definite, $A^p$ is also positive definite.
  have h_pos_def : (A ^ p).mat.PosDef := by
    have h_pos_def : ∀ p : ℝ, A.mat.PosDef → (A ^ p).mat.PosDef := by
      intro p hA_pos_def
      have h_eigenvalues_pos : ∀ i, 0 < (A.H.eigenvalues i) ^ p := by
        exact fun i => Real.rpow_pos_of_pos ( by exact Matrix.PosDef.eigenvalues_pos hA i ) _;
      have h_eigenvalues_pos : (A ^ p).mat.PosDef ↔ ∀ i, 0 < (A ^ p).H.eigenvalues i := by
        exact Matrix.IsHermitian.posDef_iff_eigenvalues_pos (H (A ^ p));
      have h_eigenvalues_pos : ∃ e : d ≃ d, (A ^ p).H.eigenvalues = fun i => (A.H.eigenvalues (e i)) ^ p := by
        exact Matrix.IsHermitian.cfc_eigenvalues (H A) fun x => x.rpow p;
      aesop;
    exact h_pos_def p hA;
  convert Matrix.nonsing_inv_mul _ _;
  exact isUnit_iff_ne_zero.mpr h_pos_def.det_pos.ne'

open ComplexOrder in
lemma isUnit_rpow_toMat (hA : A.mat.PosDef) (p : ℝ) : IsUnit (A ^ p).mat := by
  have hA_inv : IsUnit (A ^ (-p)).mat := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p
    exact Matrix.isUnit_of_right_inverse hA_inv;
  -- Since $(A^{-p}) (A^p) = 1$, we have that $(A^p)$ is the inverse of $(A^{-p})$.
  have hA_inv : (A ^ p).mat = (A ^ (-p)).mat⁻¹ := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p;
    exact Eq.symm (Matrix.inv_eq_right_inv hA_inv);
  aesop

open ComplexOrder in
lemma sandwich_inv (hB : B.mat.PosDef) :
    (A.conj (B ^ (-1/2 : ℝ)).mat)⁻¹ = A⁻¹.conj (B ^ (1/2 : ℝ)).mat := by
  have h_inv : (B ^ (-1 / 2 : ℝ)).mat⁻¹ = (B ^ (1 / 2 : ℝ)).mat := by
    apply Matrix.inv_eq_right_inv
    rw [← rpow_neg_mul_rpow_self hB (1 / 2), neg_div 2 1]
  simp [inv_conj (isUnit_rpow_toMat hB _), h_inv]

theorem ker_rpow_eq_of_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) (hp : r ≠ 0):
    (A ^ r).ker = A.ker := by
  apply ker_cfc_eq_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

theorem ker_rpow_le_of_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) :
    (A ^ r).ker ≤ A.ker := by
  apply ker_cfc_le_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

/-
For a positive Hermitian matrix A, (A^2)^(p/2) = A^p, expressed using functional calculus.
TODO: Cleanup, generalize...
-/
theorem cfc_sq_rpow_eq_cfc_rpow
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (p : ℝ) (hp : 0 < p) :
    (A ^ 2).cfc (fun x => x ^ (p/2)) = A.cfc (fun x => x ^ p) := by
  have h_sqrt : (A ^ 2).cfc (fun x => x ^ (p / 2)) = (A.cfc (fun x => x ^ 2)).cfc (fun x => x ^ (p / 2)) := by
    convert rfl;
    exact cfc_pow A;
  rw [ h_sqrt ];
  have h_sqrt : ∀ (f g : ℝ → ℝ), Continuous f → Continuous g → ∀ (A : HermitianMat d ℂ), (A.cfc f).cfc g = A.cfc (fun x => g (f x)) := by
    exact fun f g a a A => Eq.symm (cfc_comp_apply A f g);
  rw [ h_sqrt ];
  · have h_sqrt : ∀ x : ℝ, 0 ≤ x → (x ^ 2) ^ (p / 2) = x ^ p := by
      intro x hx
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx ]
      ring_nf
    exact cfc_congr_of_nonneg hA h_sqrt;
  · continuity;
  · exact continuous_id.rpow_const fun x => Or.inr <| by positivity

/-- Tr[A^p] = ∑ᵢ λᵢ^p for a Hermitian matrix A. -/
lemma trace_rpow_eq_sum (A : HermitianMat d ℂ) (p : ℝ) :
    (A ^ p).trace = ∑ i, (A.H.eigenvalues i) ^ p := by
  exact A.trace_cfc_eq (· ^ p)

/-! ## Loewner-Heinz Theorem
The operator monotonicity of `x ↦ x ^ q` for `0 < q ≤ 1`:
if `A ≤ B` (in the Loewner order), then `A ^ q ≤ B ^ q`.
This is proved using the resolvent integral representation, following the same
approach as `log_mono` in `LogExp.lean`. The key identity is:
  `x ^ q = c_q * ∫ t in (0,∞), t ^ (q-1) * x / (x + t) dt`
where `c_q = sin(π q) / π`. Since each integrand `x / (x + t)` is operator
monotone (via `inv_antitone`), the integral is operator monotone.
-/
section LoewnerHeinz

variable {A B : HermitianMat d ℂ} {q : ℝ}

open MeasureTheory ComplexOrder Filter in
/-- Finite integral approximation for the rpow monotonicity proof.
    Same integrand as `logApprox` but with weight `t ^ q`. -/
noncomputable def rpowApprox (A : HermitianMat d ℂ) (q T : ℝ) : HermitianMat d ℂ :=
  ∫ t in (0)..T, t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹)

set_option maxHeartbeats 800000 in
open MeasureTheory ComplexOrder in
theorem rpowApprox_mono {A B : HermitianMat d ℂ} (hA : A.mat.PosDef) (hB : B.mat.PosDef)
    (hAB : A ≤ B) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) :
    rpowApprox A q T ≤ rpowApprox B q T := by
  unfold HermitianMat.rpowApprox
  have h_integral_mono : ∀ᵐ t ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc 0 T), t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) ≤ t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (B + t • 1)⁻¹) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have h_inv_antitone : (B + t • 1)⁻¹ ≤ (A + t • 1)⁻¹ := by
      apply inv_antitone
      · exact hA.add_posSemidef ( Matrix.PosSemidef.smul ( Matrix.PosSemidef.one ) ht.1.le )
      · exact add_le_add_right hAB _
    exact smul_le_smul_of_nonneg_left (sub_le_sub_left h_inv_antitone _) (Real.rpow_nonneg ht.1.le q)
  rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ] at *
  refine MeasureTheory.integral_mono_ae ?_ ?_ h_integral_mono
  · refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
    have h_cont : ContinuousOn (fun t : ℝ => t ^ q) (Set.Icc 0 T) := by
      exact continuousOn_id.rpow_const fun x hx => Or.inr <| by linarith;
    have h_cont_inv : ContinuousOn (fun t : ℝ => (A + t • 1 : Matrix d d ℂ)⁻¹) (Set.Icc 0 T) := by
      have h_cont_inv : ∀ t ∈ Set.Icc 0 T, (A + t • 1 : Matrix d d ℂ).PosDef := by
        intro t ht
        exact hA.add_posSemidef (Matrix.PosSemidef.one.smul ht.1)
      have h_cont_inv : ContinuousOn (fun t : ℝ => (A + t • 1 : Matrix d d ℂ)⁻¹) (Set.Icc 0 T) := by
        have h_det_cont : ContinuousOn (fun t : ℝ => Matrix.det (A + t • 1 : Matrix d d ℂ)) (Set.Icc 0 T) := by
          fun_prop (disch := solve_by_elim)
        have h_adj_cont : ContinuousOn (fun t : ℝ => Matrix.adjugate (A + t • 1 : Matrix d d ℂ)) (Set.Icc 0 T) := by
          fun_prop (disch := solve_by_elim)
        simp_all [Matrix.inv_def]
        exact ContinuousOn.smul ( h_det_cont.inv₀ fun t ht => by specialize h_cont_inv t ht.1 ht.2; exact h_cont_inv.det_pos.ne' ) h_adj_cont
      exact h_cont_inv
    have h_cont_inv : ContinuousOn (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1 : Matrix d d ℂ)⁻¹) (Set.Icc 0 T) := by
      exact ContinuousOn.sub ( ContinuousOn.smul ( ContinuousOn.inv₀ ( continuousOn_const.add continuousOn_id ) fun t ht => by linarith [ ht.1 ] ) continuousOn_const ) h_cont_inv
    convert h_cont.smul h_cont_inv using 1
    ext
    exact continuousOn_iff_coe _
  · have h_cont_tq : ContinuousOn (fun t : ℝ => t ^ q) (Set.Icc 0 T) := by
      exact continuousOn_id.rpow_const fun x hx => Or.inr hq
    have h_cont_inv : ContinuousOn (fun t : ℝ => (B + t • 1)⁻¹) (Set.Icc 0 T) := by
      have h_cont_inv : ∀ t ∈ Set.Icc 0 T, (B + t • 1).mat.PosDef := by
        intro t ht
        exact hB.add_posSemidef (Matrix.PosSemidef.one.rsmul ht.1)
      have h_det_cont : ContinuousOn (fun t : ℝ => (B + t • 1).mat.det) (Set.Icc 0 T) := by
        fun_prop (disch := solve_by_elim)
      have h_adj_cont : ContinuousOn (fun t : ℝ => (B + t • 1).mat.adjugate) (Set.Icc 0 T) := by
        fun_prop (disch := solve_by_elim)
      have h_inv_cont : ContinuousOn (fun t : ℝ => (B + t • 1).mat⁻¹) (Set.Icc 0 T) := by
        have h_inv_cont : ∀ t ∈ Set.Icc 0 T, (B + t • 1).mat⁻¹ = (B + t • 1).mat.det⁻¹ • (B + t • 1).mat.adjugate := by
          intro t ht
          simp [Matrix.inv_def]
        exact ContinuousOn.congr ( ContinuousOn.smul ( h_det_cont.inv₀ fun t ht => ne_of_gt <| h_cont_inv t ht |> fun h => h.det_pos ) h_adj_cont ) h_inv_cont
      exact (continuousOn_iff_coe fun t => (B + t • 1)⁻¹).mpr h_inv_cont
    exact (h_cont_tq.smul ((((continuousOn_const.add continuousOn_id).inv₀ (by grind)).smul
      continuousOn_const).sub h_cont_inv)).integrableOn_Icc.mono_set (Set.Ioc_subset_Icc_self)

open MeasureTheory ComplexOrder in
/-- The scalar function underlying rpowApprox via the CFC. -/
noncomputable def scalarRpowApprox (q T x : ℝ) : ℝ :=
  ∫ t in (0)..T, t ^ q * (1 / (1 + t) - 1 / (x + t))

open MeasureTheory ComplexOrder in
theorem rpowApprox_eq_cfc_scalar (A : HermitianMat d ℂ) (hA : A.mat.PosDef) (q T : ℝ)
    (hq : 0 ≤ q) (hT : 0 < T) :
    rpowApprox A q T = A.cfc (scalarRpowApprox q T) := by
  have rpowApprox_eq_cfc_scalar : ∀ t ∈ Set.Ioc 0 T, t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) = A.cfc (fun u => t ^ q * (1 / (1 + t) - 1 / (u + t))) := by
    intro t ht
    have h_integrand : ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) = A.cfc (fun u => (1 + t)⁻¹ - (u + t)⁻¹) := by
      have h_integrand : (A + t • 1)⁻¹ = A.cfc (fun u => (u + t)⁻¹) := by
        have h_inv : (A + t • 1)⁻¹ = A.cfc (fun u => (u + t)⁻¹) := by
          have h_inv_def : (A + t • 1)⁻¹ = (A.cfc (fun u => u + t))⁻¹ := by
            rw [ show ( fun u => u + t ) = ( fun u => u ) + fun u => t from rfl, cfc_add ] ; aesop;
          have h_inv_comp : (A.cfc (fun u => u + t))⁻¹ = A.cfc (fun u => (u + t)⁻¹) := by
            have h_inv_smul : ∀ {f : ℝ → ℝ} (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0), (A.cfc f)⁻¹ = A.cfc (fun u => (f u)⁻¹) := by
              exact fun {f} hf => inv_cfc_eq_cfc_inv f hf
            apply h_inv_smul
            intro i
            have h_eigenvalue_pos : 0 < A.H.eigenvalues i := by
              exact Matrix.PosDef.eigenvalues_pos hA i
            exact ne_of_gt (add_pos h_eigenvalue_pos ht.left);
          rw [h_inv_def, h_inv_comp];
        exact h_inv
      rw [ h_integrand, ← cfc_const ];
      rw [ ← cfc_sub ];
      rfl;
    aesop;
  -- Apply the fact that the integral of a CFC is the CFC of the integral.
  have rpowApprox_integral_eq : ∫ t in (0)..T, A.cfc (fun u => t ^ q * (1 / (1 + t) - 1 / (u + t))) = A.cfc (fun u => ∫ t in (0)..T, t ^ q * (1 / (1 + t) - 1 / (u + t))) := by
    have h_integrable : ∀ u : d, IntervalIntegrable (fun t : ℝ => t ^ q * (1 / (1 + t) - 1 / (A.H.eigenvalues u + t))) MeasureTheory.volume 0 T := by
      intro u
      have h_integrable : IntervalIntegrable (fun t : ℝ => t ^ q * (1 / (1 + t) - 1 / (A.H.eigenvalues u + t))) MeasureTheory.volume 0 T := by
        have h_pos : 0 < A.H.eigenvalues u := by
          exact Matrix.PosDef.eigenvalues_pos hA u
        exact ContinuousOn.intervalIntegrable ( by exact ContinuousOn.mul ( continuousOn_id.rpow_const fun x hx => Or.inr <| by linarith ) <| ContinuousOn.sub ( continuousOn_const.div ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ Set.mem_Icc.mp <| by simpa [ hT.le ] using hx ] ) ( continuousOn_const.div ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ Set.mem_Icc.mp <| by simpa [ hT.le ] using hx ] ) ) ..;
      exact h_integrable
    exact integral_cfc_eq_cfc_integral _ _ _ h_integrable
  unfold HermitianMat.rpowApprox scalarRpowApprox; simp_all +singlePass;
  rw [ ← rpowApprox_integral_eq, intervalIntegral.integral_of_le hT.le, MeasureTheory.integral_Ioc_eq_integral_Ioo ] at *
  rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => rpowApprox_eq_cfc_scalar t ht.1 ht.2.le ]
  simp [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hT.le ]

/-- The positive constant arising from the resolvent integral.
    Equal to `∫ u in Set.Ioi 0, u ^ (q-1) / (1+u)` = `π / sin(π q)`,
    but we only need its positivity. -/
noncomputable def rpowConst (q : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), (u ^ (q - 1) / (1 + u) : ℝ)

open MeasureTheory in
/-- The integrand `u ^ (q-1) / (1+u)` is integrable on `(0, ∞)` for `0 < q < 1`. -/
lemma rpowConst_integrableOn (hq : 0 < q) (hq1 : q < 1) :
    IntegrableOn (fun u : ℝ => u ^ (q - 1) / (1 + u)) (Set.Ioi 0) := by
  sorry

/- The resolvent constant is positive. -/
lemma rpowConst_pos (hq : 0 < q) (hq1 : q < 1) : 0 < rpowConst q := by
  unfold rpowConst;
  have h_nonzero : 0 < ∫ u in Set.Ioi (0 : ℝ), u ^ (q - 1) / (1 + u) := by
    have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (q - 1) / (1 + u)) (Set.Ioi (0 : ℝ)) := by
      exact rpowConst_integrableOn hq hq1
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
    · simp [Function.support]
      exact lt_of_lt_of_le ( by norm_num ) ( MeasureTheory.measure_mono <| show Set.Ioi ( 0 : ℝ ) ⊆ { x : ℝ | ¬x ^ ( q - 1 ) = 0 ∧ ¬1 + x = 0 } ∩ Set.Ioi 0 from fun x hx => ⟨ ⟨ ne_of_gt <| Real.rpow_pos_of_pos hx _, ne_of_gt <| add_pos zero_lt_one hx ⟩, hx ⟩ );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using div_nonneg ( Real.rpow_nonneg hu.out.le _ ) ( add_nonneg zero_le_one hu.out.le );
    · exact h_integrable;
  linarith

open MeasureTheory in
/-- Key substitution identity:
    `∫ t^(q-1) * x/(x+t) dt = x^q * ∫ u^(q-1)/(1+u) du`.
    Proved by the change of variables `t = x * u`. -/
lemma integral_rpow_substitution {x : ℝ} (hx : 0 < x) (hq : 0 < q) (hq1 : q < 1) :
    ∫ t in Set.Ioi (0 : ℝ), (t ^ (q - 1) * (x / (x + t)) : ℝ) =
    x ^ q * rpowConst q := by
  sorry

open MeasureTheory Filter in
/-- The scalar rpow approximation converges pointwise.
    `scalarRpowApprox q T x → rpowConst q * (x^q - 1)` as `T → ∞`. -/
lemma scalarRpowApprox_tendsto {x : ℝ} (hx : 0 < x) (hq : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto (fun T => scalarRpowApprox q T x) atTop (nhds (rpowConst q * (x ^ q - 1))) := by
  sorry

open MeasureTheory ComplexOrder Filter in
/-- The matrix rpow approximation converges: `rpowApprox A q T → rpowConst q • (A^q - 1)`. -/
lemma tendsto_rpowApprox (hA : A.mat.PosDef) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (rpowApprox A q) atTop (nhds (rpowConst q • (A ^ q - 1))) := by
  sorry

open MeasureTheory ComplexOrder Filter in
theorem rpow_le_rpow_of_posDef (hA : A.mat.PosDef) (hAB : A ≤ B)
    (hq : 0 < q) (hq1 : q ≤ 1) : A ^ q ≤ B ^ q := by
  by_cases hq_eq_one : q = 1;
  · aesop;
  · have h_rpow : rpowConst q • (A ^ q - 1) ≤ rpowConst q • (B ^ q - 1) := by
      convert le_of_tendsto_of_tendsto ( tendsto_rpowApprox hA hq ( lt_of_le_of_ne hq1 hq_eq_one ) ) ( tendsto_rpowApprox ( posDef_of_posDef_le hA hAB ) hq ( lt_of_le_of_ne hq1 hq_eq_one ) ) _ using 1
      generalize_proofs at *; (
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using rpowApprox_mono hA ( posDef_of_posDef_le hA hAB ) hAB hq.le T hT |> le_trans <| by aesop;);
    have h_rpow_pos : 0 < rpowConst q := by
      exact rpowConst_pos hq ( lt_of_le_of_ne hq1 hq_eq_one );
    simp_all

open ComplexOrder Filter in
/-- The **Löwner—Heinz theorem**: for matrices A and B, if `0 ≤ A ≤ B` and `0 < q ≤ 1`,
then `A^q ≤ B^q`. That is, real roots are operator monotone. -/
theorem rpow_le_rpow_of_le (hA : 0 ≤ A) (hAB : A ≤ B)
    (hq : 0 < q) (hq1 : q ≤ 1) : A ^ q ≤ B ^ q := by
  -- For ε > 0, let Aε = A + ε • 1 and Bε = B + ε • 1.
  set Aε : ℝ → HermitianMat d ℂ := fun ε => A + ε • 1
  set Bε : ℝ → HermitianMat d ℂ := fun ε => B + ε • 1
  -- For ε > 0, Aε and Bε are positive definite and Aε ≤ Bε.
  have h_pos_def : ∀ ε > 0, (Aε ε).mat.PosDef ∧ (Bε ε).mat.PosDef ∧ Aε ε ≤ Bε ε := by
    intro ε hε_pos
    have h_pos_def_Aε : (Aε ε).mat.PosDef := by
      constructor <;> norm_num [ hε_pos, hA, hAB ];
      · exact H (Aε ε)
      · intro x hx_nonzero
        have h_inner : star x ⬝ᵥ (Aε ε).mat.mulVec x = star x ⬝ᵥ A.mat.mulVec x + ε * star x ⬝ᵥ x := by
          simp [ Aε, Matrix.add_mulVec]
          ring_nf
          simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm];
          simp [ Matrix.one_apply]
        have h_inner_nonneg : 0 ≤ star x ⬝ᵥ A.mat.mulVec x := by
          exact inner_mulVec_nonneg hA x
        have h_inner_pos : 0 < star x ⬝ᵥ x := by
          simp_all
        exact h_inner.symm ▸ add_pos_of_nonneg_of_pos h_inner_nonneg ( mul_pos ( mod_cast hε_pos ) ( mod_cast h_inner_pos ) ) |> lt_of_lt_of_le <| le_rfl;
    have h_pos_def_Bε : (Bε ε).mat.PosDef := by
      convert posDef_of_posDef_le h_pos_def_Aε _ using 1
      exact add_le_add_right hAB _ |> le_trans ( by simp [ Aε ] ) ;
    have h_le_Aε_Bε : Aε ε ≤ Bε ε := by
      exact add_le_add_right hAB _ |> le_trans <| by simp [ Bε ] ;
    exact ⟨h_pos_def_Aε, h_pos_def_Bε, h_le_Aε_Bε⟩
  -- By the continuity of the function $M \mapsto M^q$, we have $(Aε ε)^q \to A^q$ and $(Bε ε)^q \to B^q$ as $\epsilon \to 0^+$.
  have h_cont : Filter.Tendsto (fun ε => (Aε ε) ^ q) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A ^ q)) ∧ Filter.Tendsto (fun ε => (Bε ε) ^ q) (nhdsWithin 0 (Set.Ioi 0)) (nhds (B ^ q)) := by
    have h_cont : ContinuousOn (fun M : HermitianMat d ℂ => M ^ q) (Set.univ : Set (HermitianMat d ℂ)) := by
      -- Apply the continuity of the function $M \mapsto M^q$ on the set of all Hermitian matrices.
      apply rpow_const_continuous hq.le |> Continuous.continuousOn
    refine' ⟨ h_cont.continuousAt ( by simp ) |> fun h => h.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto' _ _ _ _ ), h_cont.continuousAt ( by simp ) |> fun h => h.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto' _ _ _ _ ) ⟩ <;> continuity;
  -- By the continuity of the function $M \mapsto M^q$, we have $(Aε ε)^q \leq (Bε ε)^q$ for all $\epsilon > 0$.
  have h_le : ∀ ε > 0, (Aε ε) ^ q ≤ (Bε ε) ^ q := by
    exact fun ε hε => rpow_le_rpow_of_posDef ( h_pos_def ε hε |>.1 ) ( h_pos_def ε hε |>.2.2 ) hq hq1 |> le_trans <| by simp [ * ] ;
  exact le_of_tendsto_of_tendsto h_cont.1 h_cont.2 ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_le ε hε ) |> fun h => by simpa using h;

end LoewnerHeinz

section ArakiLiebThirring

variable {A B : HermitianMat d ℂ} {q r : ℝ}

/-- An inequality of Lieb-Thirring type. For 0 < r ≤ 1:
  `Tr[B^r A^r B^r] ≤ Tr[(B A B)^r]`.
-/
lemma lieb_thirring_le_one
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {r : ℝ} (hq0 : 0 < r) (hq1 : q ≤ r) :
    ((A ^ r).conj (B ^ r).mat).trace ≤ ((A.conj B.mat) ^ r).trace := by
  sorry

end ArakiLiebThirring

/-
Trace subadditivity (Rotfel'd inequality): for PSD A, B and 0 < p ≤ 1,
Tr[(A + B)^p] ≤ Tr[A^p] + Tr[B^p].

This isn't needed for anything else in the repository atm, but it would
be nice to have as a fact.

A stronger version states it as a majorization theorem. See
e.g. https://www.math.uwaterloo.ca/~hwolkowi/henry/reports/thesismingmay613.pdf
-/
lemma trace_rpow_add_le
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ((A + B) ^ p).trace ≤ (A ^ p).trace + (B ^ p).trace := by
  sorry
