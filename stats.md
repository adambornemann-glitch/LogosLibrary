# Library Statistics: `LogosLibrary`

**Root:** `/Users/augustusthwack/Desktop/logos_library/LogosLibrary`

**Files:** 263 `.lean` files

## Summary

| Metric | Count |
|--------|------:|
| Total raw lines | 99,806 |
| Lines of code (no block comments, no blanks, no `--`-only) | 42,787 |
| Blank lines | 17,619 |
| Comment-only lines (`--`) | 3,080 |
| Lines inside `/- -/` block comments | 44,577 |

## Declarations

| Kind | Count |
|------|------:|
| `theorem` | 2,658 |
| `lemma` | 794 |
| `def` | 1,273 |
| `axiom` | 101 |
| `structure` | 375 |
| `class` | 5 |
| `instance` | 20 |
| `abbrev` | 12 |
| `inductive` | 22 |
| **Proofs (theorem + lemma)** | **3,452** |
| **Definitions (def + abbrev)** | **1,285** |
| **Axioms** | **101** |
| **Types (structure + class + inductive)** | **402** |

## File Listing

| # | File | Raw Lines | Code Lines | Thm+Lem | Def | Axiom |
|--:|------|----------:|----------:|--------:|----:|------:|
| 1 | `Basic.lean` | 1 | 1 | 0 | 1 | 0 |
| 2 | `InformationGeometry.lean` | 2 | 2 | 0 | 0 | 0 |
| 3 | `InformationGeometry/CramerRao.lean` | 10 | 4 | 0 | 0 | 0 |
| 4 | `InformationGeometry/CramerRao/Basic.lean` | 196 | 88 | 1 | 3 | 0 |
| 5 | `InformationGeometry/CramerRao/Bound.lean` | 227 | 157 | 2 | 0 | 0 |
| 6 | `InformationGeometry/CramerRao/CauchySchwarz.lean` | 280 | 227 | 2 | 0 | 0 |
| 7 | `InformationGeometry/CramerRao/Cross.lean` | 354 | 221 | 9 | 0 | 0 |
| 8 | `InformationGeometry/Fisher.lean` | 11 | 5 | 0 | 0 | 0 |
| 9 | `InformationGeometry/Fisher/FisherInformation.lean` | 513 | 274 | 19 | 5 | 0 |
| 10 | `InformationGeometry/Fisher/FisherMetric.lean` | 470 | 248 | 17 | 4 | 0 |
| 11 | `InformationGeometry/Fisher/Score.lean` | 345 | 176 | 15 | 1 | 0 |
| 12 | `InformationGeometry/Fisher/StatisticalManifold.lean` | 340 | 149 | 15 | 8 | 0 |
| 13 | `InformationGeometry/Fisher/StatisticalModel.lean` | 325 | 142 | 9 | 7 | 0 |
| 14 | `InformationGeometry/file.lean` | 500 | 160 | 18 | 4 | 0 |
| 15 | `QuantumComputing.lean` | 10 | 5 | 0 | 0 | 0 |
| 16 | `QuantumComputing/PvNP/ComputationEmbedding.lean` | 916 | 350 | 25 | 10 | 0 |
| 17 | `QuantumComputing/PvNP/CostBlind.lean` | 438 | 141 | 15 | 6 | 0 |
| 18 | `QuantumComputing/PvNP/LocalityBound.lean` | 682 | 162 | 7 | 0 | 0 |
| 19 | `QuantumComputing/PvNP/PhaseTransition.lean` | 822 | 248 | 8 | 3 | 0 |
| 20 | `QuantumComputing/PvNP/SymmetryBreaking.lean` | 614 | 179 | 9 | 5 | 0 |
| 21 | `QuantumComputing/ThermalTuringMachine/Core.lean` | 515 | 227 | 14 | 17 | 0 |
| 22 | `QuantumComputing/ThermalTuringMachine/Lemmas.lean` | 400 | 262 | 44 | 1 | 0 |
| 23 | `QuantumComputing/ThermalTuringMachine/OneBit.lean` | 665 | 236 | 15 | 11 | 0 |
| 24 | `QuantumComputing/ThermalTuringMachine/Simple.lean` | 382 | 98 | 13 | 10 | 0 |
| 25 | `QuantumComputing/ThermalTuringMachine/Simplex.lean` | 495 | 85 | 10 | 11 | 0 |
| 26 | `QuantumMechanics.lean` | 11 | 5 | 0 | 0 | 0 |
| 27 | `QuantumMechanics/BellsTheorem.lean` | 11 | 5 | 0 | 0 | 0 |
| 28 | `QuantumMechanics/BellsTheorem/Basic.lean` | 422 | 264 | 10 | 16 | 0 |
| 29 | `QuantumMechanics/BellsTheorem/CHSH_bounds.lean` | 10 | 4 | 0 | 0 | 0 |
| 30 | `QuantumMechanics/BellsTheorem/CHSH_bounds/CHSH_Basic.lean` | 456 | 357 | 18 | 0 | 0 |
| 31 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Commuting.lean` | 74 | 51 | 1 | 0 | 0 |
| 32 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Op_square.lean` | 276 | 215 | 13 | 1 | 0 |
| 33 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Separable.lean` | 187 | 128 | 1 | 0 | 0 |
| 34 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Tsirelson.lean` | 31 | 1 | 0 | 0 | 0 |
| 35 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Tsirelson/CommutatorAlgebra.lean` | 452 | 375 | 17 | 0 | 0 |
| 36 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Tsirelson/Tsirelson.lean` | 322 | 246 | 8 | 0 | 0 |
| 37 | `QuantumMechanics/BellsTheorem/CHSH_bounds/Tsirelson/UnitaryBounds.lean` | 269 | 206 | 10 | 0 | 0 |
| 38 | `QuantumMechanics/BellsTheorem/LHV.lean` | 270 | 145 | 7 | 6 | 0 |
| 39 | `QuantumMechanics/BellsTheorem/QuantumCHSH.lean` | 34 | 4 | 0 | 0 | 0 |
| 40 | `QuantumMechanics/BellsTheorem/QuantumCHSH/Correlations.lean` | 151 | 110 | 4 | 6 | 0 |
| 41 | `QuantumMechanics/BellsTheorem/QuantumCHSH/Q_CHSH_Basic.lean` | 112 | 76 | 8 | 6 | 0 |
| 42 | `QuantumMechanics/BellsTheorem/QuantumCHSH/Tsirelson.lean` | 44 | 32 | 1 | 0 | 0 |
| 43 | `QuantumMechanics/BellsTheorem/QuantumCHSH/Violation.lean` | 53 | 34 | 2 | 2 | 0 |
| 44 | `QuantumMechanics/ModularTheory.lean` | 10 | 4 | 0 | 0 | 0 |
| 45 | `QuantumMechanics/ModularTheory/Cocycle.lean` | 527 | 206 | 6 | 7 | 0 |
| 46 | `QuantumMechanics/ModularTheory/KMS.lean` | 3 | 3 | 0 | 0 | 0 |
| 47 | `QuantumMechanics/ModularTheory/KMS/Condition.lean` | 373 | 164 | 10 | 6 | 0 |
| 48 | `QuantumMechanics/ModularTheory/KMS/Modular.lean` | 367 | 200 | 8 | 5 | 0 |
| 49 | `QuantumMechanics/ModularTheory/KMS/PeriodicStrip.lean` | 871 | 595 | 15 | 9 | 0 |
| 50 | `QuantumMechanics/ModularTheory/RelativeModular.lean` | 377 | 168 | 7 | 6 | 1 |
| 51 | `QuantumMechanics/ModularTheory/ThermalTime.lean` | 520 | 193 | 11 | 9 | 1 |
| 52 | `QuantumMechanics/ModularTheory/TomitaTakesaki.lean` | 789 | 429 | 27 | 15 | 0 |
| 53 | `QuantumMechanics/SpectralTheory.lean` | 12 | 6 | 0 | 0 | 0 |
| 54 | `QuantumMechanics/SpectralTheory/BochnerRoute.lean` | 37 | 4 | 0 | 0 | 0 |
| 55 | `QuantumMechanics/SpectralTheory/BochnerRoute/FourierUniqueness.lean` | 788 | 476 | 31 | 2 | 0 |
| 56 | `QuantumMechanics/SpectralTheory/BochnerRoute/PdProperties.lean` | 404 | 197 | 29 | 2 | 0 |
| 57 | `QuantumMechanics/SpectralTheory/BochnerRoute/PositiveDefinite.lean` | 94 | 30 | 1 | 2 | 2 |
| 58 | `QuantumMechanics/SpectralTheory/BochnerRoute/SpectralMeasure.lean` | 423 | 271 | 21 | 3 | 0 |
| 59 | `QuantumMechanics/SpectralTheory/BochnerRoute/UnitaryConnection.lean` | 231 | 109 | 7 | 2 | 0 |
| 60 | `QuantumMechanics/SpectralTheory/CayleyTransform.lean` | 68 | 7 | 0 | 0 | 0 |
| 61 | `QuantumMechanics/SpectralTheory/CayleyTransform/Eigenvalue.lean` | 247 | 214 | 4 | 0 | 0 |
| 62 | `QuantumMechanics/SpectralTheory/CayleyTransform/Inverse.lean` | 302 | 252 | 9 | 1 | 0 |
| 63 | `QuantumMechanics/SpectralTheory/CayleyTransform/Mobius.lean` | 82 | 43 | 8 | 0 | 0 |
| 64 | `QuantumMechanics/SpectralTheory/CayleyTransform/SpectralMeasure.lean` | 158 | 95 | 6 | 4 | 0 |
| 65 | `QuantumMechanics/SpectralTheory/CayleyTransform/Spectrum.lean` | 603 | 556 | 7 | 0 | 0 |
| 66 | `QuantumMechanics/SpectralTheory/CayleyTransform/Transform.lean` | 441 | 388 | 11 | 1 | 0 |
| 67 | `QuantumMechanics/SpectralTheory/CayleyTransform/Unitary.lean` | 353 | 290 | 14 | 2 | 0 |
| 68 | `QuantumMechanics/SpectralTheory/DiracEquation.lean` | 128 | 7 | 0 | 0 | 0 |
| 69 | `QuantumMechanics/SpectralTheory/DiracEquation/CliffordAlgebra.lean` | 703 | 337 | 35 | 8 | 0 |
| 70 | `QuantumMechanics/SpectralTheory/DiracEquation/Conservation.lean` | 259 | 64 | 2 | 4 | 4 |
| 71 | `QuantumMechanics/SpectralTheory/DiracEquation/Current.lean` | 302 | 107 | 4 | 8 | 0 |
| 72 | `QuantumMechanics/SpectralTheory/DiracEquation/GammaTraces.lean` | 553 | 304 | 27 | 3 | 0 |
| 73 | `QuantumMechanics/SpectralTheory/DiracEquation/Operators.lean` | 254 | 67 | 4 | 2 | 3 |
| 74 | `QuantumMechanics/SpectralTheory/DiracEquation/PauliMatrices.lean` | 150 | 42 | 9 | 3 | 0 |
| 75 | `QuantumMechanics/SpectralTheory/DiracEquation/SpectralTheory.lean` | 512 | 211 | 6 | 11 | 4 |
| 76 | `QuantumMechanics/SpectralTheory/FunctionalCalc.lean` | 64 | 9 | 0 | 0 | 0 |
| 77 | `QuantumMechanics/SpectralTheory/FunctionalCalc/Agreement.lean` | 112 | 49 | 1 | 0 | 4 |
| 78 | `QuantumMechanics/SpectralTheory/FunctionalCalc/Algebraic.lean` | 477 | 370 | 18 | 2 | 1 |
| 79 | `QuantumMechanics/SpectralTheory/FunctionalCalc/BoundedFunctionalCalc.lean` | 346 | 204 | 17 | 1 | 0 |
| 80 | `QuantumMechanics/SpectralTheory/FunctionalCalc/CrossMeasure.lean` | 494 | 351 | 22 | 2 | 1 |
| 81 | `QuantumMechanics/SpectralTheory/FunctionalCalc/Domain.lean` | 313 | 186 | 14 | 3 | 0 |
| 82 | `QuantumMechanics/SpectralTheory/FunctionalCalc/Generator.lean` | 170 | 90 | 3 | 2 | 5 |
| 83 | `QuantumMechanics/SpectralTheory/FunctionalCalc/Integral.lean` | 177 | 91 | 3 | 0 | 10 |
| 84 | `QuantumMechanics/SpectralTheory/FunctionalCalc/ScalarMeasure.lean` | 336 | 240 | 14 | 0 | 0 |
| 85 | `QuantumMechanics/SpectralTheory/FunctionalCalc/SpectralProjection.lean` | 269 | 170 | 23 | 0 | 0 |
| 86 | `QuantumMechanics/SpectralTheory/RelThermo.lean` | 983 | 344 | 18 | 1 | 4 |
| 87 | `QuantumMechanics/SpectralTheory/ResolventRoute.lean` | 54 | 4 | 0 | 0 | 0 |
| 88 | `QuantumMechanics/SpectralTheory/ResolventRoute/ResolventKernel.lean` | 313 | 164 | 6 | 3 | 6 |
| 89 | `QuantumMechanics/SpectralTheory/ResolventRoute/SpectralRepresentation.lean` | 150 | 49 | 3 | 0 | 5 |
| 90 | `QuantumMechanics/SpectralTheory/ResolventRoute/StieltjesInversion.lean` | 187 | 79 | 1 | 0 | 3 |
| 91 | `QuantumMechanics/SpectralTheory/ResolventRoute/StonesFormula.lean` | 213 | 91 | 1 | 0 | 5 |
| 92 | `QuantumMechanics/Uncertainty.lean` | 11 | 5 | 0 | 0 | 0 |
| 93 | `QuantumMechanics/Uncertainty/CramerRao.lean` | 399 | 136 | 5 | 0 | 0 |
| 94 | `QuantumMechanics/Uncertainty/Heisenberg.lean` | 79 | 19 | 1 | 1 | 0 |
| 95 | `QuantumMechanics/Uncertainty/Robertson.lean` | 201 | 112 | 7 | 0 | 0 |
| 96 | `QuantumMechanics/Uncertainty/Schrodinger.lean` | 250 | 144 | 5 | 1 | 0 |
| 97 | `QuantumMechanics/Uncertainty/UnboundedOperators.lean` | 275 | 148 | 14 | 14 | 0 |
| 98 | `QuantumMechanics/UnitaryEvo.lean` | 12 | 6 | 0 | 0 | 0 |
| 99 | `QuantumMechanics/UnitaryEvo/Bochner.lean` | 47 | 4 | 0 | 0 | 0 |
| 100 | `QuantumMechanics/UnitaryEvo/Bochner/Basic.lean` | 315 | 255 | 10 | 0 | 0 |
| 101 | `QuantumMechanics/UnitaryEvo/Bochner/Domain.lean` | 501 | 413 | 19 | 6 | 0 |
| 102 | `QuantumMechanics/UnitaryEvo/Bochner/Limits.lean` | 31 | 3 | 0 | 0 | 0 |
| 103 | `QuantumMechanics/UnitaryEvo/Bochner/Limits/Helpers.lean` | 222 | 187 | 4 | 0 | 0 |
| 104 | `QuantumMechanics/UnitaryEvo/Bochner/Limits/Minus.lean` | 558 | 525 | 3 | 0 | 0 |
| 105 | `QuantumMechanics/UnitaryEvo/Bochner/Limits/Plus.lean` | 343 | 310 | 3 | 0 | 0 |
| 106 | `QuantumMechanics/UnitaryEvo/Bochner/Resolvent.lean` | 146 | 87 | 8 | 2 | 0 |
| 107 | `QuantumMechanics/UnitaryEvo/Generator.lean` | 252 | 160 | 9 | 1 | 0 |
| 108 | `QuantumMechanics/UnitaryEvo/Resolvent.lean` | 44 | 8 | 0 | 0 | 0 |
| 109 | `QuantumMechanics/UnitaryEvo/Resolvent/Analytic.lean` | 148 | 107 | 1 | 0 | 0 |
| 110 | `QuantumMechanics/UnitaryEvo/Resolvent/Basic.lean` | 236 | 167 | 11 | 5 | 0 |
| 111 | `QuantumMechanics/UnitaryEvo/Resolvent/Core.lean` | 238 | 204 | 1 | 1 | 0 |
| 112 | `QuantumMechanics/UnitaryEvo/Resolvent/Identities.lean` | 199 | 148 | 5 | 1 | 0 |
| 113 | `QuantumMechanics/UnitaryEvo/Resolvent/LowerBound.lean` | 111 | 77 | 1 | 0 | 0 |
| 114 | `QuantumMechanics/UnitaryEvo/Resolvent/NormExpansion.lean` | 182 | 110 | 10 | 0 | 0 |
| 115 | `QuantumMechanics/UnitaryEvo/Resolvent/Range.lean` | 30 | 3 | 0 | 0 | 0 |
| 116 | `QuantumMechanics/UnitaryEvo/Resolvent/Range/ClosedRange.lean` | 239 | 202 | 3 | 0 | 0 |
| 117 | `QuantumMechanics/UnitaryEvo/Resolvent/Range/Orthogonal.lean` | 239 | 197 | 4 | 0 | 0 |
| 118 | `QuantumMechanics/UnitaryEvo/Resolvent/Range/Surjectivity.lean` | 149 | 100 | 3 | 1 | 0 |
| 119 | `QuantumMechanics/UnitaryEvo/Resolvent/SpecialCases.lean` | 325 | 263 | 11 | 2 | 0 |
| 120 | `QuantumMechanics/UnitaryEvo/Schrodinger.lean` | 66 | 22 | 1 | 0 | 0 |
| 121 | `QuantumMechanics/UnitaryEvo/Stone.lean` | 238 | 140 | 7 | 0 | 0 |
| 122 | `QuantumMechanics/UnitaryEvo/Yosida.lean` | 51 | 1 | 0 | 0 | 0 |
| 123 | `QuantumMechanics/UnitaryEvo/Yosida/Basic.lean` | 85 | 49 | 8 | 0 | 0 |
| 124 | `QuantumMechanics/UnitaryEvo/Yosida/Bounds.lean` | 108 | 81 | 3 | 0 | 0 |
| 125 | `QuantumMechanics/UnitaryEvo/Yosida/Convergence.lean` | 19 | 1 | 0 | 0 | 0 |
| 126 | `QuantumMechanics/UnitaryEvo/Yosida/Convergence/Approximants.lean` | 233 | 189 | 7 | 0 | 0 |
| 127 | `QuantumMechanics/UnitaryEvo/Yosida/Convergence/JNegOperator.lean` | 171 | 139 | 3 | 0 | 0 |
| 128 | `QuantumMechanics/UnitaryEvo/Yosida/Convergence/JOperator.lean` | 162 | 122 | 3 | 0 | 0 |
| 129 | `QuantumMechanics/UnitaryEvo/Yosida/Defs.lean` | 95 | 42 | 1 | 7 | 0 |
| 130 | `QuantumMechanics/UnitaryEvo/Yosida/Duhamel.lean` | 21 | 1 | 0 | 0 | 0 |
| 131 | `QuantumMechanics/UnitaryEvo/Yosida/Duhamel/Commutation.lean` | 82 | 53 | 3 | 0 | 0 |
| 132 | `QuantumMechanics/UnitaryEvo/Yosida/Duhamel/Estimate.lean` | 227 | 189 | 4 | 0 | 0 |
| 133 | `QuantumMechanics/UnitaryEvo/Yosida/Duhamel/Formula.lean` | 274 | 230 | 5 | 1 | 0 |
| 134 | `QuantumMechanics/UnitaryEvo/Yosida/Duhamel/Helpers.lean` | 153 | 101 | 6 | 0 | 0 |
| 135 | `QuantumMechanics/UnitaryEvo/Yosida/ExpBounded.lean` | 21 | 1 | 0 | 0 | 0 |
| 136 | `QuantumMechanics/UnitaryEvo/Yosida/ExpBounded/Adjoint.lean` | 166 | 125 | 6 | 0 | 0 |
| 137 | `QuantumMechanics/UnitaryEvo/Yosida/ExpBounded/Basic.lean` | 247 | 188 | 11 | 1 | 0 |
| 138 | `QuantumMechanics/UnitaryEvo/Yosida/ExpBounded/Unitary.lean` | 214 | 171 | 8 | 0 | 0 |
| 139 | `QuantumMechanics/UnitaryEvo/Yosida/Exponential.lean` | 435 | 366 | 7 | 1 | 0 |
| 140 | `QuantumMechanics/UnitaryEvo/Yosida/Symmetry.lean` | 100 | 62 | 2 | 0 | 0 |
| 141 | `Relativity.lean` | 11 | 5 | 0 | 0 | 0 |
| 142 | `Relativity/GR/Forbidden.lean` | 11 | 5 | 0 | 0 | 0 |
| 143 | `Relativity/GR/Forbidden/AngularMomentum.lean` | 267 | 151 | 9 | 11 | 0 |
| 144 | `Relativity/GR/Forbidden/LifeTime.lean` | 321 | 183 | 12 | 11 | 1 |
| 145 | `Relativity/GR/Forbidden/MeasureZero.lean` | 235 | 104 | 8 | 8 | 0 |
| 146 | `Relativity/GR/Forbidden/Reductio.lean` | 324 | 178 | 9 | 9 | 0 |
| 147 | `Relativity/GR/Forbidden/ThermalExcitation.lean` | 170 | 68 | 5 | 6 | 0 |
| 148 | `Relativity/GR/Kerr.lean` | 11 | 5 | 0 | 0 | 0 |
| 149 | `Relativity/GR/Kerr/Complexity.lean` | 410 | 149 | 8 | 3 | 3 |
| 150 | `Relativity/GR/Kerr/Extensions.lean` | 487 | 326 | 14 | 6 | 2 |
| 151 | `Relativity/GR/Kerr/Metric.lean` | 496 | 274 | 11 | 12 | 0 |
| 152 | `Relativity/GR/Kerr/Singularity.lean` | 192 | 96 | 5 | 1 | 0 |
| 153 | `Relativity/GR/Kerr/TODO.lean` | 314 | 4 | 0 | 0 | 0 |
| 154 | `Relativity/GR/Kerr/Thermodynamics.lean` | 357 | 126 | 5 | 5 | 1 |
| 155 | `Relativity/SR/MinkowskiSpacetime.lean` | 467 | 253 | 17 | 15 | 0 |
| 156 | `Relativity/Thermodynamics/Jacobson.lean` | 818 | 328 | 51 | 20 | 0 |
| 157 | `Relativity/Thermodynamics/Ott.lean` | 776 | 413 | 54 | 4 | 0 |
| 158 | `StochasticCalculus/PVariation.lean` | 7 | 1 | 0 | 0 | 0 |
| 159 | `StochasticCalculus/PVariation/Basic.lean` | 600 | 339 | 16 | 5 | 0 |
| 160 | `StochasticCalculus/PVariation/TODO.lean` | 42 | 0 | 0 | 0 | 0 |
| 161 | `StochasticCalculus/SewingLemma.lean` | 416 | 165 | 16 | 5 | 0 |
| 162 | `Superior.lean` | 12 | 6 | 0 | 0 | 0 |
| 163 | `Superior/Bridges.lean` | 11 | 5 | 0 | 0 | 0 |
| 164 | `Superior/Bridges/CProcess.lean` | 531 | 129 | 14 | 2 | 0 |
| 165 | `Superior/Bridges/Gravity/EGtoSD.lean` | 839 | 207 | 26 | 0 | 0 |
| 166 | `Superior/Bridges/Gravity/LQGtoEQ.lean` | 917 | 186 | 34 | 0 | 0 |
| 167 | `Superior/Bridges/Gravity/LQGtoSD.lean` | 815 | 164 | 30 | 1 | 0 |
| 168 | `Superior/Bridges/Gravity/Synthesis.lean` | 956 | 164 | 13 | 0 | 0 |
| 169 | `Superior/CommonResources.lean` | 14 | 8 | 0 | 0 | 0 |
| 170 | `Superior/CommonResources/CliffordPeriodicity.lean` | 13 | 7 | 0 | 0 | 0 |
| 171 | `Superior/CommonResources/CliffordPeriodicity/Basic.lean` | 189 | 48 | 2 | 3 | 0 |
| 172 | `Superior/CommonResources/CliffordPeriodicity/Clock.lean` | 503 | 162 | 39 | 9 | 0 |
| 173 | `Superior/CommonResources/CliffordPeriodicity/Dimensions.lean` | 158 | 63 | 8 | 5 | 0 |
| 174 | `Superior/CommonResources/CliffordPeriodicity/Mobius.lean` | 195 | 57 | 10 | 2 | 0 |
| 175 | `Superior/CommonResources/CliffordPeriodicity/Signature.lean` | 480 | 144 | 29 | 4 | 0 |
| 176 | `Superior/CommonResources/CliffordPeriodicity/SpinorData.lean` | 149 | 53 | 8 | 2 | 0 |
| 177 | `Superior/CommonResources/CliffordPeriodicity/Table.lean` | 423 | 200 | 8 | 18 | 0 |
| 178 | `Superior/CommonResources/DivisionAlgebra/Basic.lean` | 693 | 251 | 51 | 16 | 0 |
| 179 | `Superior/CommonResources/DivisionAlgebra/Quaternions.lean` | 526 | 184 | 40 | 14 | 0 |
| 180 | `Superior/CommonResources/GenerationsTheorem.lean` | 496 | 90 | 11 | 5 | 1 |
| 181 | `Superior/CommonResources/HopfTower.lean` | 10 | 4 | 0 | 0 | 0 |
| 182 | `Superior/CommonResources/HopfTower/FanoPlane.lean` | 9 | 3 | 0 | 0 | 0 |
| 183 | `Superior/CommonResources/HopfTower/FanoPlane/BoolMap.lean` | 408 | 193 | 14 | 0 | 0 |
| 184 | `Superior/CommonResources/HopfTower/FanoPlane/Defs.lean` | 439 | 170 | 8 | 27 | 0 |
| 185 | `Superior/CommonResources/HopfTower/FanoPlane/G2Automorph.lean` | 473 | 224 | 12 | 0 | 4 |
| 186 | `Superior/CommonResources/HopfTower/HopfFibration.lean` | 892 | 288 | 50 | 11 | 6 |
| 187 | `Superior/CommonResources/HopfTower/HopfTowerKnot.lean` | 1,099 | 420 | 53 | 18 | 0 |
| 188 | `Superior/CommonResources/HopfTower/HopfTowerOctonion.lean` | 1,002 | 378 | 38 | 15 | 0 |
| 189 | `Superior/CommonResources/ModularFlow.lean` | 619 | 167 | 33 | 11 | 0 |
| 190 | `Superior/CommonResources/Quintet.lean` | 513 | 166 | 26 | 4 | 0 |
| 191 | `Superior/CommonResources/Time/SuperCausets.lean` | 111 | 5 | 0 | 0 | 0 |
| 192 | `Superior/CommonResources/Time/SuperCausets/Basic.lean` | 786 | 191 | 25 | 6 | 0 |
| 193 | `Superior/CommonResources/Time/SuperCausets/Cosmology.lean` | 813 | 210 | 26 | 7 | 0 |
| 194 | `Superior/CommonResources/Time/SuperCausets/QuaternionicEntropy.lean` | 582 | 184 | 37 | 13 | 0 |
| 195 | `Superior/CommonResources/Time/SuperCausets/Synthesis.lean` | 661 | 271 | 8 | 0 | 0 |
| 196 | `Superior/CommonResources/Time/SuperCausets/ThermalCauset.lean` | 451 | 111 | 10 | 0 | 0 |
| 197 | `Superior/CommonResources/Time/ThermalTime.lean` | 10 | 4 | 0 | 0 | 0 |
| 198 | `Superior/CommonResources/Time/ThermalTime/Basic.lean` | 589 | 282 | 29 | 11 | 0 |
| 199 | `Superior/CommonResources/Time/ThermalTime/Consistency.lean` | 123 | 86 | 8 | 3 | 0 |
| 200 | `Superior/CommonResources/Time/ThermalTime/InfoTheory.lean` | 162 | 84 | 14 | 11 | 0 |
| 201 | `Superior/CommonResources/Time/ThermalTime/Measurement.lean` | 182 | 83 | 10 | 8 | 0 |
| 202 | `Superior/HotGravity.lean` | 11 | 5 | 0 | 0 | 0 |
| 203 | `Superior/HotGravity/EntropicGravity.lean` | 137 | 5 | 0 | 0 | 0 |
| 204 | `Superior/HotGravity/EntropicGravity/Clausius.lean` | 833 | 225 | 34 | 7 | 0 |
| 205 | `Superior/HotGravity/EntropicGravity/EntropicForce.lean` | 963 | 317 | 65 | 15 | 0 |
| 206 | `Superior/HotGravity/EntropicGravity/Horizons.lean` | 651 | 257 | 55 | 17 | 0 |
| 207 | `Superior/HotGravity/EntropicGravity/Recovery.lean` | 1,094 | 357 | 64 | 17 | 0 |
| 208 | `Superior/HotGravity/EntropicGravity/Synthesis.lean` | 924 | 256 | 35 | 10 | 0 |
| 209 | `Superior/HotGravity/LoopQuantumGravity.lean` | 13 | 7 | 0 | 0 | 0 |
| 210 | `Superior/HotGravity/LoopQuantumGravity/EPRLVertex.lean` | 1,544 | 703 | 38 | 28 | 0 |
| 211 | `Superior/HotGravity/LoopQuantumGravity/MasterTheorem.lean` | 735 | 188 | 14 | 0 | 0 |
| 212 | `Superior/HotGravity/LoopQuantumGravity/ModularTheory.lean` | 1,378 | 536 | 37 | 33 | 0 |
| 213 | `Superior/HotGravity/LoopQuantumGravity/QuantumTetrahedron.lean` | 946 | 398 | 25 | 23 | 0 |
| 214 | `Superior/HotGravity/LoopQuantumGravity/SU2Rep.lean` | 1,147 | 362 | 38 | 30 | 0 |
| 215 | `Superior/HotGravity/LoopQuantumGravity/SpinFoam.lean` | 1,040 | 414 | 33 | 24 | 0 |
| 216 | `Superior/HotGravity/LoopQuantumGravity/SpinNetwork.lean` | 988 | 415 | 22 | 24 | 0 |
| 217 | `Superior/HotGravity/NanoThermo.lean` | 47 | 4 | 0 | 0 | 0 |
| 218 | `Superior/HotGravity/NanoThermo/Biconditional.lean` | 107 | 46 | 4 | 0 | 0 |
| 219 | `Superior/HotGravity/NanoThermo/Definition.lean` | 936 | 262 | 33 | 5 | 0 |
| 220 | `Superior/HotGravity/NanoThermo/Limits.lean` | 304 | 93 | 10 | 0 | 0 |
| 221 | `Superior/HotGravity/NanoThermo/Monotonicity.lean` | 273 | 78 | 7 | 0 | 0 |
| 222 | `Superior/HotGravity/NanoThermo/PageCurve.lean` | 622 | 145 | 16 | 5 | 0 |
| 223 | `Superior/HotGravity/ObjectiveReduction.lean` | 8 | 2 | 0 | 0 | 0 |
| 224 | `Superior/HotGravity/ObjectiveReduction/ChemicalMeasurement.lean` | 520 | 187 | 15 | 15 | 0 |
| 225 | `Superior/HotGravity/ObjectiveReduction/EProcess.lean` | 341 | 191 | 18 | 10 | 0 |
| 226 | `Superior/HotGravity/ShapeDynamics.lean` | 49 | 2 | 0 | 0 | 0 |
| 227 | `Superior/HotGravity/ShapeDynamics/EntropicTime.lean` | 673 | 222 | 52 | 8 | 0 |
| 228 | `Superior/HotGravity/ShapeDynamics/Synthesis.lean` | 772 | 252 | 51 | 14 | 0 |
| 229 | `Superior/KnotTheory.lean` | 10 | 4 | 0 | 0 | 0 |
| 230 | `Superior/KnotTheory/Knots/MinKnotExtended.lean` | 893 | 267 | 30 | 14 | 3 |
| 231 | `Superior/KnotTheory/Knots/MinimumKnot.lean` | 709 | 211 | 23 | 21 | 0 |
| 232 | `Superior/KnotTheory/Strings.lean` | 100 | 5 | 0 | 0 | 0 |
| 233 | `Superior/KnotTheory/Strings/Basic.lean` | 492 | 150 | 28 | 14 | 0 |
| 234 | `Superior/KnotTheory/Strings/Quaternion.lean` | 301 | 84 | 15 | 3 | 0 |
| 235 | `Superior/KnotTheory/Strings/Synthesis.lean` | 232 | 59 | 1 | 0 | 0 |
| 236 | `Superior/KnotTheory/Strings/Thermal.lean` | 392 | 144 | 13 | 2 | 0 |
| 237 | `Superior/KnotTheory/Strings/Topology.lean` | 583 | 222 | 16 | 15 | 4 |
| 238 | `Superior/KnotTheory/YangMills.lean` | 310 | 49 | 1 | 0 | 0 |
| 239 | `Superior/KnotTheory/YangMills/EntropyManifold.lean` | 1,011 | 340 | 36 | 21 | 0 |
| 240 | `Superior/KnotTheory/YangMills/TopologicalMassGap.lean` | 977 | 306 | 31 | 22 | 2 |
| 241 | `Superior/SpectralTriples.lean` | 9 | 3 | 0 | 0 | 0 |
| 242 | `Superior/SpectralTriples/GeometricUnity.lean` | 10 | 4 | 0 | 0 | 0 |
| 243 | `Superior/SpectralTriples/GeometricUnity/ComputingLambda.lean` | 1,004 | 379 | 36 | 15 | 1 |
| 244 | `Superior/SpectralTriples/GeometricUnity/ObserverseLagrangian.lean` | 1,876 | 549 | 60 | 29 | 3 |
| 245 | `Superior/SpectralTriples/GeometricUnity/ShiabComponents.lean` | 544 | 200 | 34 | 8 | 0 |
| 246 | `Superior/SpectralTriples/GeometricUnity/ShiabOperator.lean` | 1,639 | 625 | 59 | 31 | 0 |
| 247 | `Superior/SpectralTriples/SpectralBridge.lean` | 850 | 201 | 18 | 3 | 0 |
| 248 | `Superior/SpectralTriples/Triples.lean` | 10 | 4 | 0 | 0 | 0 |
| 249 | `Superior/SpectralTriples/Triples/ConcreteSpectrum.lean` | 1,271 | 396 | 44 | 15 | 0 |
| 250 | `Superior/SpectralTriples/Triples/ProductGeometry.lean` | 1,263 | 364 | 40 | 9 | 1 |
| 251 | `Superior/SpectralTriples/Triples/SpectralAction.lean` | 1,280 | 327 | 30 | 17 | 1 |
| 252 | `Superior/SpectralTriples/Triples/SpectralDefs.lean` | 1,232 | 379 | 63 | 19 | 0 |
| 253 | `Superior/SplitMechanics.lean` | 14 | 3 | 0 | 0 | 0 |
| 254 | `Superior/SplitMechanics/BohmianMech.lean` | 801 | 280 | 42 | 11 | 1 |
| 255 | `Superior/SplitMechanics/ItFromSplit.lean` | 911 | 382 | 28 | 12 | 8 |
| 256 | `Superior/SplitMechanics/ThermalBell.lean` | 12 | 6 | 0 | 0 | 0 |
| 257 | `Superior/SplitMechanics/ThermalBell/CHSH.lean` | 351 | 220 | 14 | 3 | 0 |
| 258 | `Superior/SplitMechanics/ThermalBell/Constraints.lean` | 358 | 257 | 17 | 13 | 0 |
| 259 | `Superior/SplitMechanics/ThermalBell/Core.lean` | 165 | 79 | 2 | 6 | 0 |
| 260 | `Superior/SplitMechanics/ThermalBell/DecayGap.lean` | 399 | 80 | 17 | 1 | 0 |
| 261 | `Superior/SplitMechanics/ThermalBell/Entropy.lean` | 167 | 92 | 9 | 6 | 0 |
| 262 | `Superior/SplitMechanics/ThermalBell/Geometry.lean` | 263 | 132 | 28 | 15 | 0 |
| 263 | `Superior/SplitMechanics/ThermalBell/Tsirelson.lean` | 478 | 222 | 34 | 10 | 0 |

## Top 20 Files by Code Lines

| # | File | Code Lines |
|--:|------|----------:|
| 1 | `Superior/HotGravity/LoopQuantumGravity/EPRLVertex.lean` | 703 |
| 2 | `Superior/SpectralTriples/GeometricUnity/ShiabOperator.lean` | 625 |
| 3 | `QuantumMechanics/ModularTheory/KMS/PeriodicStrip.lean` | 595 |
| 4 | `QuantumMechanics/SpectralTheory/CayleyTransform/Spectrum.lean` | 556 |
| 5 | `Superior/SpectralTriples/GeometricUnity/ObserverseLagrangian.lean` | 549 |
| 6 | `Superior/HotGravity/LoopQuantumGravity/ModularTheory.lean` | 536 |
| 7 | `QuantumMechanics/UnitaryEvo/Bochner/Limits/Minus.lean` | 525 |
| 8 | `QuantumMechanics/SpectralTheory/BochnerRoute/FourierUniqueness.lean` | 476 |
| 9 | `QuantumMechanics/ModularTheory/TomitaTakesaki.lean` | 429 |
| 10 | `Superior/CommonResources/HopfTower/HopfTowerKnot.lean` | 420 |
| 11 | `Superior/HotGravity/LoopQuantumGravity/SpinNetwork.lean` | 415 |
| 12 | `Superior/HotGravity/LoopQuantumGravity/SpinFoam.lean` | 414 |
| 13 | `QuantumMechanics/UnitaryEvo/Bochner/Domain.lean` | 413 |
| 14 | `Relativity/Thermodynamics/Ott.lean` | 413 |
| 15 | `Superior/HotGravity/LoopQuantumGravity/QuantumTetrahedron.lean` | 398 |
| 16 | `Superior/SpectralTriples/Triples/ConcreteSpectrum.lean` | 396 |
| 17 | `QuantumMechanics/SpectralTheory/CayleyTransform/Transform.lean` | 388 |
| 18 | `Superior/SplitMechanics/ItFromSplit.lean` | 382 |
| 19 | `Superior/SpectralTriples/GeometricUnity/ComputingLambda.lean` | 379 |
| 20 | `Superior/SpectralTriples/Triples/SpectralDefs.lean` | 379 |

## Top 20 Files by Proof Count (theorem + lemma)

| # | File | Proofs |
|--:|------|-------:|
| 1 | `Superior/HotGravity/EntropicGravity/EntropicForce.lean` | 65 |
| 2 | `Superior/HotGravity/EntropicGravity/Recovery.lean` | 64 |
| 3 | `Superior/SpectralTriples/Triples/SpectralDefs.lean` | 63 |
| 4 | `Superior/SpectralTriples/GeometricUnity/ObserverseLagrangian.lean` | 60 |
| 5 | `Superior/SpectralTriples/GeometricUnity/ShiabOperator.lean` | 59 |
| 6 | `Superior/HotGravity/EntropicGravity/Horizons.lean` | 55 |
| 7 | `Relativity/Thermodynamics/Ott.lean` | 54 |
| 8 | `Superior/CommonResources/HopfTower/HopfTowerKnot.lean` | 53 |
| 9 | `Superior/HotGravity/ShapeDynamics/EntropicTime.lean` | 52 |
| 10 | `Relativity/Thermodynamics/Jacobson.lean` | 51 |
| 11 | `Superior/CommonResources/DivisionAlgebra/Basic.lean` | 51 |
| 12 | `Superior/HotGravity/ShapeDynamics/Synthesis.lean` | 51 |
| 13 | `Superior/CommonResources/HopfTower/HopfFibration.lean` | 50 |
| 14 | `QuantumComputing/ThermalTuringMachine/Lemmas.lean` | 44 |
| 15 | `Superior/SpectralTriples/Triples/ConcreteSpectrum.lean` | 44 |
| 16 | `Superior/SplitMechanics/BohmianMech.lean` | 42 |
| 17 | `Superior/CommonResources/DivisionAlgebra/Quaternions.lean` | 40 |
| 18 | `Superior/SpectralTriples/Triples/ProductGeometry.lean` | 40 |
| 19 | `Superior/CommonResources/CliffordPeriodicity/Clock.lean` | 39 |
| 20 | `Superior/CommonResources/HopfTower/HopfTowerOctonion.lean` | 38 |
