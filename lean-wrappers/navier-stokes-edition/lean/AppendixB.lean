import AppendixBTail
import Breakdown.Cert.ExtendedCoerciveMain
import Breakdown.CertCell.CellLayerClosed
import Breakdown.CertCell.CertPivotCount
import Breakdown.CertCell.CertTreeLowerBound
import Breakdown.CellReduction.CellLayerBreakdownClosed

open scoped ContDiff ENNReal
open MeasureTheory Matrix
open Breakdown Breakdown.PieceWeights Breakdown.CertCell

noncomputable section
namespace NavierStokes

section Multiplier
open Breakdown.CoerciveWeak

/-- Proposition B.1 in the formal weak-perturbation class. Admissible weights,
a regular reference field with a supplied weak Hessian, square-integrable
periodic actuators and a square-integrable periodic right-hand side produce
a divergence-free multiplier, finite mu-seminorm, the multiplier norm bound,
and the density inequality. The constants c and w₀ are retained as parameters;
setting c = 3/50 and w = w₀ = 39/50 gives the paper's constants. The last
inequality uses positive and negative parts, so it remains meaningful before
finiteness of the positive part has been proved. -/
theorem proposition_B_1 :
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤),
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∃ M, m.IsMultiplierField v G H M ∧
        m.seminormSq P v < ⊤ ∧
        periodNorm M ≤ Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.seminormSq P v).toReal) ∧
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, densityPosWith m P h w v G H W HW σ y)
            + ENNReal.ofReal (-m.multiplierGap P w act v G H κ F M)
          ≤ ENNReal.ofReal (m.multiplierGap P w act v G H κ F M)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, densityNegWith m P h w v G H W HW σ y := by
  exact Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_proof

/-- Lemma B.2. The multiplier density estimate and the remaining row inequality
imply the coercive estimate (7.18). The two displayed scalar budgets specify
the constants multiplying the right-hand-side norm and the pin values.
The regularity, admissibility and row hypotheses are required for every
parameter in the formal parameter set. -/
theorem lemma_B_2 {k : ℕ} {d : ExtendedCertificateData k}
    (hrad : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j)
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (d.actuatorBound ^ 2))
    (HW : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : (Fin k → ℝ) → ℝ)
    (hmodel : ∀ q ∈ d.params, IsWeakSecondDerivState (d.model q) (HW q) (D q))
    {C : Type} {nE nM : ℕ} (m : (Fin k → ℝ) → PieceWeights C nE nM)
    (hs : (Fin k → ℝ) → HarmonicBounds)
    {c cμ t epsSup epsGradSup ratio : ℝ}
    (hc : ∀ q ∈ d.params, (m q).c = c) (hcμ : ∀ q ∈ d.params, (m q).cμ = cμ) (ht : 0 ≤ t)
    (hm : ∀ q ∈ d.params, IsAdmissibleWeak (m q) (d.period q) (hs q) d.weightFn (d.model q) (HW q)
      d.weight epsSup epsGradSup ratio)
    (hrest : RowRestClause d m hs HW c t)
    (hL2 : Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)
      / Real.sqrt c ≤ d.coerciveL2)
    (hPin : Real.sqrt (t / c) ≤ d.coercivePin) :
    ExtendedCoerciveClause d := by
  exact Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData_proved
    hrad hwup hactm hactp hnorm HW D hmodel m hs hc hcμ ht hm hrest hL2 hPin

end Multiplier

section HalfPlane
open Breakdown.CertCell.Bridge

/-- Lemma B.3. For the formal reflection and axial-mode symmetries, the full
space-time positive and negative density integrals each equal 4π times the
corresponding integral over the quarter plane. These two identities also
hold when an integral is infinite. When the negative part is finite they
justify the signed form (B.23), with no subtraction of two infinities. -/
theorem lemma_B_3 :
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (D₀ : ℝ),
    IsModeClass D.cert.symmetries D.azimuthOrder → IsFlipInvariantModel D.given D.givenHess →
    CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess D₀ →
    (∀ q ∈ D.cert.params, HasMeasurableBoundData (D.pieces q) (D.bounds q)) →
    (∀ q ∈ D.cert.params, IsFlipCompatible (D.pieces q) (D.bounds q) D.cert.weightFn) →
    ∀ q ∈ D.cert.params, (∃ e₁ e₂ e₃ : ℝ, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃) →
    ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityPosWith (D.pieces q) (D.cert.period q) (D.bounds q)
          D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formPos q v G H ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, CoerciveWeak.densityNegWith (D.pieces q) (D.cert.period q) (D.bounds q)
          D.cert.weightFn v G H D.given D.givenHess σ y) = ENNReal.ofReal (4 * Real.pi) * D.formNeg q v G H := by
  exact Breakdown.CertCell.modeDensityBridge_closed

end HalfPlane

/-- Proposition B.4 in the formal cell representation. The full cell-system
conditions imply finite negative density, the inequality for each cell,
vanishing of absent modes, the exterior bound and a compatible pressure and
tree state. Cell inequalities are expressed using positive and negative
parts and the explicit pressure/cell-state coordinates. The four real
remainders printed as r_{Q,0},...,r_{Q,3} are not introduced by this statement;
the source expresses their contributions as row shares, strain slack,
credit and actuator cost. -/
theorem proposition_B_4 {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CellLayerSystem.CoerciveNumbers)
    (B : CellLayerSystem.ReductionEntries k)
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B) :
    FormNegFinite D D.coercivity ∧ CellCalculus.CellFormBoundsHold D R ∧
      CellJunctions D R N.globalError T := by
  have hJ := cellJunctions_closed D X R T N.globalError h.cell h.shape_valueSets Y h.entry_conditions
  have hL := CellLayerSystem.layerJunctionFacts_of_parts h
  obtain ⟨b, hb⟩ := hL.model_state
  obtain ⟨E, hE⟩ := h.cell.continuum_conditions_given.coefficients
  have hN : FormNegFinite D D.coercivity :=
    formNegFinite D D.coercivity b (by have := h.cell.azimuth_ge; omega)
      (coefficientLowerBounds_of_entries D E hE h.cell.box_uniform.c_eq
        (admissible_of_hypothesis cellLayerParts_closed.instance_parts D X R T N.globalError h.cell hL)) hb
  exact ⟨hN, cellFormAssembly_closed D R h.cell.cell_conditions hJ.cell_residual, hJ⟩

section Modes
open Breakdown.CertCell.TailBand

/-- Lemma B.5. Every perturbation mode satisfies the four angular derivative
inequalities (B.35), almost everywhere. Under the formal coefficient test on
a region, its charged density is nonnegative there. Frequencies are
`labelAzimuth mm ι`; derivative arrays use Frobenius squares. The second
component states the consequence of (B.36) and (B.29), rather than naming the
paper's intermediate scalar expression f₁*. -/
theorem lemma_B_5 :
  (∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P → ∀ (mm : ℕ) (ι : ℤ × ℤ),
    ∀ᵐ p ∂(volume.restrict halfPlane), AngularRelations |(labelAzimuth mm ι : ℝ)| p.1
      (Real.sqrt (cnormSq (labelHess mm ι H p))) (Real.sqrt (cnormSq (curlGradOfSecondDeriv (labelHess mm ι H p))))
      (Real.sqrt (cnormSq (labelGrad mm ι G p))) (Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))))
      (Real.sqrt (cnormSq (labelVel mm ι v p)))) ∧
  (∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ),
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    ∀ (mm : ℕ) (E : OffModeCondition C nE nM), ∀ mc : ModeCharges, IsOffModeCondition m P h w mc mm E →
    ∀ (Γ : Set Symmetry) v G H g, IsPerturbation Γ P v G H g → ∀ ι ∈ E.modes,
      ∀ᵐ p ∂(volume.restrict E.region), 0 ≤ offModeDensity m P h w mc E.charges mm ι v G H p) := by
  exact ⟨angularModeBounds, Breakdown.CertCell.Assembly.offModeConditionSound_holds⟩

end Modes

section Tree
open Breakdown.CertCell.Certificate Breakdown.CellCert.Finite

namespace BSevenAlgebra

/-- Elementary quadratic-form identity used to expose the column-kernel conclusion of Lemma B.7. -/
theorem quadValue_add_matrix {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M + N) x = quadValue M x + quadValue N x := by
  simp [quadValue, add_mulVec, dotProduct_add]

/-- Elementary quadratic-form identity used to expose the column-kernel conclusion of Lemma B.7. -/
theorem quadValue_sub_matrix {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M - N) x = quadValue M x - quadValue N x := by
  simp [quadValue, sub_mulVec, dotProduct_sub]

/-- Elementary quadratic-form identity used to expose the column-kernel conclusion of Lemma B.7. -/
theorem quadValue_sum_matrix {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (M : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (∑ k ∈ s, M k) x = ∑ k ∈ s, quadValue (M k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadValue]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quadValue_add_matrix, ih]

/-- Elementary quadratic-form identity used to expose the column-kernel conclusion of Lemma B.7. -/
theorem quadValue_diagonal_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (d x : ι → ℝ) :
    quadValue (diagonal d) x = ∑ j, d j * x j ^ 2 := by
  simp only [quadValue, dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Elementary quadratic-form identity used to expose the column-kernel conclusion of Lemma B.7. -/
theorem quadValue_vecMulVec_self {ι : Type*} [Fintype ι] (c x : ι → ℝ) :
    quadValue (vecMulVec c c) x = (c ⬝ᵥ x) ^ 2 := by
  simp only [quadValue, vecMulVec_mulVec]
  simp [dotProduct_smul, dotProduct_comm x c, sq]


end BSevenAlgebra

open BSevenAlgebra

/-- Lemma B.7. The leaf form dominates the root/pivot/column form. Every
nonzero vector orthogonal to all negative columns has strictly positive leaf
form; the positive subspace has dimension at least the number of determined
variables. The root form retains the nonnegative passed root matrix, so
dropping it gives the lower bound printed in (B.41). -/
theorem lemma_B_7 (A B : Type) [Fintype A] [Fintype B]
    (T : SignedTree A B) (hT : IsSignedTree T) (hP : PassesPivotCount T) :
    (∀ x, quadValue T.rootForm x ≤ quadValue T.totalForm x) ∧
    (∀ x : A ⊕ B → ℝ, x ≠ 0 → (∀ c, T.column c ⬝ᵥ x = 0) →
      0 < quadValue T.totalForm x) ∧
    ∃ P : Submodule ℝ (A ⊕ B → ℝ), Fintype.card A ≤ Module.finrank ℝ P ∧
      IsPositiveOn T.totalForm P := by
  have hbound := Breakdown.CertCell.Certificate.signedTreeLowerBound A B T hT
  obtain ⟨P, hdim, hpos⟩ := Breakdown.CertCell.Certificate.pivotCountPositive A B T hP
  refine ⟨hbound, ?_, P, hdim, ?_⟩
  · intro x hx0 hcol
    apply lt_of_lt_of_le (b := quadValue T.rootForm x) _ (hbound x)
    classical
    let _ : Fintype T.Node := T.nodeFintype
    let _ : Fintype T.Column := T.columnFintype
    unfold SignedTree.rootForm
    rw [quadValue_sub_matrix, quadValue_add_matrix, quadValue_sum_matrix, quadValue_sum_matrix]
    simp only [quadValue_diagonal_matrix, quadValue_vecMulVec_self, hcol]
    have hzero : ∑ c : T.Column, (0 : ℝ) ^ 2 = 0 := by simp
    rw [hzero, sub_zero]
    refine add_pos_of_nonneg_of_pos (hP.root_front_nonneg x) ?_
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      exact hx0 (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    obtain ⟨ν, hν⟩ := hP.every_variable_pivoted j
    refine Finset.sum_pos' (fun μ _ => Finset.sum_nonneg (fun i _ => ?_))
      ⟨ν, Finset.mem_univ _, Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩⟩
    · split_ifs with h
      · exact mul_nonneg (hP.slack_positive _ _ h).le (sq_nonneg _)
      · simp
    · split_ifs with h
      · exact mul_nonneg (hP.slack_positive _ _ h).le (sq_nonneg _)
      · simp
    · rw [if_pos hν]
      exact mul_pos (hP.slack_positive _ _ hν) (by positivity)
  · intro x hx hx0
    exact lt_of_lt_of_le (hpos x hx hx0) (hbound x)

end Tree

section RowEstimate
open Breakdown.CoerciveWeak

/-- Proposition B.8. Complete cell-system conditions give finite negative
density and the row/constraint lower estimate (B.21), for each parameter,
periodic weak perturbation and admissible right-hand side. The weights in
the estimate are the stored coercivity and pin weight; the final cell system
specializes them to 3/50 and 1000. -/
theorem proposition_B_8 {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CellLayerSystem.CoerciveNumbers)
    (B : CellLayerSystem.ReductionEntries k)
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B) :
    RowRestClause D.cert D.pieces D.bounds D.modelHess D.coercivity D.pinWeight := by
  exact rowRestClause_closed D X R T N.globalError h.cell h.shape_valueSets Y h.entry_conditions

end RowEstimate

section Transfer
open Breakdown.CertReduction

/-- Lemma B.9. Bounds on a finite decomposition of the profile difference give
(7.19); the reference strain bound and the corresponding form-shift budget
give (7.22) for every c₃ at least the sum of the two form bounds. Choosing two
pieces, one measured in L² and one in L³, gives (B.47)-(B.48). The formal
hypotheses additionally state measurability, the gradient identities and the
regularity/decay needed to interpret all integrals. -/
theorem lemma_B_9 {k : ℕ} (d : ExtendedCertificateData k)
    (pieces : ShiftPieces k) (numbers : ModelFormNumbers)
    (hstanding : BridgeStanding d) (hgap : GapTransferBounded d pieces)
    (hshift : FormShiftBounded d pieces) (hfrozen : FrozenFormBounded d numbers)
    (c₃ : ℝ) (hc₃ : d.modelFormBound + d.formShift ≤ c₃) :
    (∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
      periodLIntegral (fun σ y => ‖G σ y (d.profile q σ y - d.model q σ y)
        + (fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y) (v σ y)‖ ^ 2) ≤
        ENNReal.ofReal (d.gapSize ^ 2 * weightedEnergy d.weightFn G H)) ∧
    (∀ q ∈ d.params, ∀ σ w G H, IsProfileField d.symmetries w G H →
      -c₃ * stationaryEnergy d.weightFn G H ≤ frozenForm (d.profile q σ) w G H) := by
  refine ⟨gapTransferBridgeHolds_proof k d pieces hstanding hgap, ?_⟩
  intro q hq σ w G H hw
  have h1 := formShiftBridgeHolds_proof k d pieces hstanding hshift q hq σ w G H hw
  have h2 := (frozenFormBridgeHolds_of_convection convectionIdentity_holds)
    k d numbers hstanding hfrozen q hq σ w G H hw
  have hE : 0 ≤ stationaryEnergy d.weightFn G H :=
    add_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
      (MeasureTheory.integral_nonneg fun y => mul_nonneg
        (show 0 ≤ d.weightFn y by rw [hstanding.weightFn_const]; exact hstanding.weight_pos.le)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hsum : -(d.modelFormBound + d.formShift) * stationaryEnergy d.weightFn G H ≤
      frozenForm (d.profile q σ) w G H := by linarith
  exact le_trans (mul_le_mul_of_nonneg_right (neg_le_neg hc₃) hE) hsum

/-- Lemma B.10. A periodic adjoint test field with a uniform spatial L³ or L²
bound controls its pairing with (v·∇)v by the weighted perturbation energy.
`cubic = true` selects 2/(√3 w₀); `cubic = false` selects c_w/√w₀.
The conclusion bounds the integral of the product of norms, so it also
bounds the absolute value of the pairing. -/
theorem lemma_B_10 :
  ∀ (Γ : Set Symmetry) (P w₀ z : ℝ) (cubic : Bool) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g ζ : ℝ → Space → Space),
    0 < w₀ → 0 ≤ z → IsPerturbation Γ P v G H g →
    AEStronglyMeasurable (fun p : ℝ × Space => ζ p.1 p.2) volume →
    (∀ σ, AdjointSizeBound cubic (ζ σ) z) →
    periodLIntegral (fun σ y => ‖G σ y (v σ y)‖ * ‖ζ σ y‖) ≤
      ENNReal.ofReal (adjointQuadCoeff w₀ cubic * z * weightedEnergy (fun _ => w₀) G H) := by
  exact adjointQuadTerm_of matrixFacts perturbationSliceHolds energyBoundsHolds_proof
    cubicWeightProductHolds periodGlue

end Transfer

section Adjoint
open Breakdown.AdjointDefect

/-- The bound proved by the authors for Lemma B.11: a field with the formal
dual bound pairs with every weak H¹ field whose gradient has finite period
energy. The conclusion includes almost-everywhere spatial integrability and
integrability of the spatial integral as a function of time, together with
the sharp dual estimate. Joint absolute integrability is a separate target. -/
theorem lemma_B_11_iterated (R : ℝ → Space → Space) (ρ : ℝ)
    (hR : DualBounded R ρ) :
  ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume →
    (∀ᵐ σ, IsWeakGradient (v σ) (G σ)) →
    (∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) < ⊤) →
    periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ →
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), Integrable (fun y => inner ℝ (v σ y) (R σ y))) ∧
      IntegrableOn (fun σ => ∫ y, inner ℝ (v σ y) (R σ y)) (Set.Icc (0 : ℝ) 1) ∧
      |periodInnerIntegral v R| ≤ ρ * gradientNorm G := by
  exact dualBoundedBound_of_parts remainderPlainHolds_proof remainderAzimuthalHolds_proof R ρ hR

/-- Lemma B.12 in the formal representation of the adjoint defect. Under the
explicit profile decomposition, adjoint regularity, potential identities,
dual remainder bounds and scalar budget, the difference between the forcing
pairing and the pin correction is at most a_j times the weighted energy
norm. `AdjointDefectBounded.total` is exactly the sum budget for the stored
defect and pin-charge quantities; no certificate-existence premise is used. -/
theorem lemma_B_12 :
  ∀ {k : ℕ} (d : ExtendedCertificateData k) (r : Fin k → AdjointDefectEntry k),
    d.weightFn = (fun _ => d.weight) → 0 < d.weight →
    (∀ j ∈ d.adjointSet, AdjointDefectStructure d j (r j)) →
    (∀ j ∈ d.adjointSet, AdjointPotentialFacts d j (r j)) →
    (∀ j ∈ d.adjointSet, AdjointDefectBounded d j (r j)) →
    ∀ j ∈ d.adjointSet, ∀ q ∈ d.params, ∀ v G H g,
      IsPerturbation d.symmetries (d.period q) v G H g → ∀ F : ℝ → Space → Space,
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile q) d.actuator 0 v G g F →
        |periodPairing F (d.adjoint j q) - ∑ l, d.coupling q j l * pinValue (d.pin l) G| ≤
          d.adjointDefect j * Real.sqrt (weightedEnergy d.weightFn G H) := by
  exact adjointDefectBridge_of_pieces (representationHolds_of_density testFieldDensityHolds_proof)
    potentialBoundHolds_proof
    (dualBoundedBound_of_parts remainderPlainHolds_proof remainderAzimuthalHolds_proof)
    pinChargeHolds_proof freeShiftBoundHolds_proof

end Adjoint

section Offset
open Breakdown.CellReduction.Instantiation Breakdown.CertCell.GivenShape

/-- Lemma B.13. The profile's constant, linear and quadratic residual
coefficients, their enclosure errors, the parameter radii and the two
exterior L² bounds yield the adjoint offset estimate (7.34). The formal
statement also requires the shape/pressure identities that establish the
coefficient expansion. The bound is stored as `adjointOffset`. -/
theorem lemma_B_13 :
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (F : GivenShapeEntry k) (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k)
    (Z : AdjointShapeEntry k) (O : OffsetExpansionEntry k),
    (∀ j, D.cert.scale j ≠ 0) →
    IsGivenShapeEntry D X F → InstantiationBounded D R Pr Z → IsOffsetExpansionEntry D R Pr Z O →
    (∀ q ∈ D.cert.params,
      periodLIntegral (fun σ y => ‖D.cert.defect q σ y‖ ^ 2) ≤ ENNReal.ofReal (D.cert.defectBound q ^ 2)) →
    (∀ j ∈ D.cert.adjointSet, ∀ q ∈ D.cert.params, ∀ σ,
      ∫⁻ y, ENNReal.ofReal (‖D.cert.adjoint j q σ y‖ ^ 2) ≤ ENNReal.ofReal (D.cert.adjointL2 j ^ 2)) →
    ∀ j ∈ D.cert.adjointSet, ∀ q ∈ D.cert.params,
      |D.cert.adjustedMultiplier q j - D.cert.scale j * q j| ≤ D.cert.adjointOffset j := by
  exact offsetClause_holds_of stepPhase_holds pressureFieldRegular_holds offsetBallIdentity_holds

end Offset

/-- Proposition B.14. Data satisfying every condition of the formal cell
system determine an extended certificate after choosing a common decay
constant. Only the numerical field `decay` is changed; the period, velocity,
reference field, actuators, residual, pins, rows and adjoint data are retained.
The conclusion is conditional on all cell conditions; it supplies no concrete
certificate data or numerical verification of those conditions. -/
theorem proposition_B_14 {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CellLayerSystem.CoerciveNumbers)
    (B : CellLayerSystem.ReductionEntries k)
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B) :
    ∃ decay : ℝ, IsExtendedCertificate ({ D.cert with decay := decay } : ExtendedCertificateData k) := by
  exact CellLayerSystem.isExtendedCertificate_of_parts
    (CellReduction.Instantiation.instantiation_holds_of_open CellReduction.Instantiation.stepPhase_holds
      CellReduction.Instantiation.movedFieldJointSmooth_holds CellReduction.Instantiation.movedFieldUniformDecay_holds
      CellReduction.Instantiation.pinValueContinuous_holds CellReduction.Instantiation.pressureFieldRegular_holds)
    (CellReduction.Instantiation.offsetClause_holds_of CellReduction.Instantiation.stepPhase_holds
      CellReduction.Instantiation.pressureFieldRegular_holds CellReduction.Instantiation.offsetBallIdentity_holds)
    CertReduction.gapTransferBridgeHolds_proof CertReduction.formShiftBridgeHolds_proof
    (CertReduction.frozenFormBridgeHolds_of_convection CertReduction.convectionIdentity_holds)
    (CertReduction.adjointQuadraticBridge_of
      (CertReduction.adjointQuadTerm_of CertReduction.matrixFacts CertReduction.perturbationSliceHolds
        CertReduction.energyBoundsHolds_proof CertReduction.cubicWeightProductHolds CertReduction.periodGlue)
      CertReduction.periodGlue)
    (AdjointDefect.adjointDefectBridge_of_pieces
      (AdjointDefect.representationHolds_of_density AdjointDefect.testFieldDensityHolds_proof)
      AdjointDefect.potentialBoundHolds_proof
      (AdjointDefect.dualBoundedBound_of_parts AdjointDefect.remainderPlainHolds_proof
        AdjointDefect.remainderAzimuthalHolds_proof)
      AdjointDefect.pinChargeHolds_proof AdjointDefect.freeShiftBoundHolds_proof)
    (CellReduction.Instantiation.adjointStructure_holds_of
      (CellReduction.Instantiation.adjointField_holds_of CellReduction.Instantiation.fieldDecayOrder_holds
        CellReduction.Instantiation.fieldPotential_holds CellReduction.Instantiation.classicalDivergenceWeak_holds)
      (CellReduction.Instantiation.profilePiecesFlow_of CellReduction.Instantiation.stepPhase_holds
        CellReduction.Instantiation.movedFieldUniformDecay_holds))
    CertReduction.smoothShiftPiecesHolds PotentialShape.potentialParts_holds h

end NavierStokes
