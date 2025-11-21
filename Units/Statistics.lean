-- Stats.lean        -- Statistical measures, tests, and information criteria
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Information.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Stats

open Units.SI Units.Information

/-
================================================================================
STATISTICAL UNITS AND MEASURES LIBRARY
================================================================================

This module provides type-safe units for statistics, hypothesis testing,
effect sizes, model selection criteria, and uncertainty quantification.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Descriptive statistics (mean, variance, std dev, skewness, kurtosis)
- Correlation and association (Pearson, Spearman, Kendall, Cramér's V)
- Hypothesis testing (p-values, test statistics, power, error rates)
- Effect sizes (Cohen's d, Glass's Δ, Hedges' g, η², ω², f²)
- Model selection (AIC, BIC, DIC, WAIC, cross-validation)
- Bayesian statistics (Bayes factors, credible intervals, posterior)
- Regression metrics (R², adjusted R², MSE, RMSE, MAE)
- Goodness of fit (χ², KS statistic, Anderson-Darling)
- Survival analysis (hazard ratios, log-rank)
- Meta-analysis (heterogeneity, forest plots)
- Resampling (bootstrap CI, jackknife, permutation)

## USAGE PATTERNS
Float: Experimental data analysis, real-time statistics, machine learning
metrics, A/B testing, clinical trials, sensor data processing, quality control,
financial analytics, bioinformatics pipelines

ℚ: Exact probability calculations, contingency tables, discrete distributions,
combinatorial statistics, exact tests (Fisher's, binomial), rational Bayes
factors, exact confidence intervals

ℝ: Theoretical statistics, asymptotic analysis, continuous distributions,
maximum likelihood theory, information geometry, statistical manifolds,
measure-theoretic probability, stochastic processes
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Statistics
================================================================================================
-/
def sqrt2_F : Float := 1.41421356237309504880
def sqrtPi_F : Float := 1.77245385090551602730
def sqrt2Pi_F : Float := 2.50662827463100050242
def ln2_F : Float := 0.693147180559945309417
def euler_gamma_F : Float := 0.577215664901532860606
def phi_F : Float := 1.61803398874989484820  -- Golden ratio

/--
================================================================================================
   Basic Statistical Measures
================================================================================================
-/
-- Mean/Average
structure Mean_F       where val : Float deriving Repr, BEq, Inhabited
structure Mean_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mean_R       where val : ℝ     deriving Inhabited

-- Variance
structure Variance_F   where val : Float deriving Repr, BEq, Inhabited
structure Variance_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Variance_R   where val : ℝ     deriving Inhabited

-- Standard Deviation (σ)
structure StdDev_F     where val : Float deriving Repr, BEq, Inhabited
structure StdDev_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StdDev_R     where val : ℝ     deriving Inhabited

-- Standard Error
structure StdError_F   where val : Float deriving Repr, BEq, Inhabited
structure StdError_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StdError_R   where val : ℝ     deriving Inhabited

-- Coefficient of Variation
structure CoeffVar_F   where val : Float deriving Repr, BEq, Inhabited
structure CoeffVar_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoeffVar_R   where val : ℝ     deriving Inhabited

-- Median
structure Median_F     where val : Float deriving Repr, BEq, Inhabited
structure Median_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Median_R     where val : ℝ     deriving Inhabited

-- Mode
structure Mode_F       where val : Float deriving Repr, BEq, Inhabited
structure Mode_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mode_R       where val : ℝ     deriving Inhabited

-- Percentile/Quantile
structure Percentile_F where
  val : Float
  p : Float  -- Which percentile (0-100)
  deriving Repr, BEq, Inhabited

structure Quantile_F where
  val : Float
  q : Float  -- Which quantile (0-1)
  deriving Repr, BEq, Inhabited

-- Inter-quartile range
structure IQR_F        where val : Float deriving Repr, BEq, Inhabited
structure IQR_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IQR_R        where val : ℝ     deriving Inhabited

-- Mean Absolute Deviation
structure MAD_F        where val : Float deriving Repr, BEq, Inhabited
structure MAD_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MAD_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Distribution Shape Measures
================================================================================================
-/
-- Skewness
structure Skewness_F   where val : Float deriving Repr, BEq, Inhabited
structure Skewness_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Skewness_R   where val : ℝ     deriving Inhabited

-- Kurtosis
structure Kurtosis_F   where val : Float deriving Repr, BEq, Inhabited
structure Kurtosis_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kurtosis_R   where val : ℝ     deriving Inhabited

-- Excess Kurtosis (Kurtosis - 3)
structure ExcessKurtosis_F where val : Float deriving Repr, BEq, Inhabited
structure ExcessKurtosis_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ExcessKurtosis_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Correlation and Association Measures
================================================================================================
-/
-- Pearson correlation coefficient (r)
structure PearsonCorr_F where val : Float deriving Repr, BEq, Inhabited
structure PearsonCorr_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PearsonCorr_R where val : ℝ     deriving Inhabited

-- Spearman rank correlation (ρ)
structure SpearmanCorr_F where val : Float deriving Repr, BEq, Inhabited
structure SpearmanCorr_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpearmanCorr_R where val : ℝ     deriving Inhabited

-- Kendall rank correlation (τ)
structure KendallTau_F where val : Float deriving Repr, BEq, Inhabited
structure KendallTau_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KendallTau_R where val : ℝ     deriving Inhabited

-- Covariance
structure Covariance_F where val : Float deriving Repr, BEq, Inhabited
structure Covariance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Covariance_R where val : ℝ     deriving Inhabited

-- Cramér's V (association for nominal variables)
structure CramersV_F   where val : Float deriving Repr, BEq, Inhabited
structure CramersV_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CramersV_R   where val : ℝ     deriving Inhabited

-- Phi coefficient (for 2x2 tables)
structure PhiCoeff_F   where val : Float deriving Repr, BEq, Inhabited
structure PhiCoeff_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhiCoeff_R   where val : ℝ     deriving Inhabited

-- Point-biserial correlation
structure PointBiserial_F where val : Float deriving Repr, BEq, Inhabited
structure PointBiserial_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PointBiserial_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Hypothesis Testing
================================================================================================
-/
-- P-value
structure PValue_F     where val : Float deriving Repr, BEq, Inhabited
structure PValue_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PValue_R     where val : ℝ     deriving Inhabited

-- Significance level (α)
structure Alpha_F      where val : Float deriving Repr, BEq, Inhabited
structure Alpha_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Alpha_R      where val : ℝ     deriving Inhabited

-- Statistical power (1-β)
structure Power_F      where val : Float deriving Repr, BEq, Inhabited
structure Power_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Power_R      where val : ℝ     deriving Inhabited

-- Type I error rate
structure TypeIError_F where val : Float deriving Repr, BEq, Inhabited
structure TypeIError_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TypeIError_R where val : ℝ     deriving Inhabited

-- Type II error rate (β)
structure TypeIIError_F where val : Float deriving Repr, BEq, Inhabited
structure TypeIIError_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TypeIIError_R where val : ℝ     deriving Inhabited

-- Z-score/standard score
structure ZScore_F     where val : Float deriving Repr, BEq, Inhabited
structure ZScore_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ZScore_R     where val : ℝ     deriving Inhabited

-- T-statistic
structure TStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure TStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TStatistic_R where val : ℝ     deriving Inhabited

-- F-statistic
structure FStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure FStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FStatistic_R where val : ℝ     deriving Inhabited

-- Chi-squared statistic
structure ChiSquared_F where val : Float deriving Repr, BEq, Inhabited
structure ChiSquared_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChiSquared_R where val : ℝ     deriving Inhabited

-- Chi-squared per degree of freedom
structure ChiSquaredPerDF_F where val : Float deriving Repr, BEq, Inhabited
structure ChiSquaredPerDF_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChiSquaredPerDF_R where val : ℝ     deriving Inhabited

-- Degrees of freedom
structure DegreesOfFreedom where val : ℕ  deriving Repr, BEq, DecidableEq, Inhabited

-- Sample size
structure SampleSize   where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

/--
================================================================================================
   Effect Sizes
================================================================================================
-/
-- Cohen's d (standardized mean difference)
structure CohensD_F    where val : Float deriving Repr, BEq, Inhabited
structure CohensD_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CohensD_R    where val : ℝ     deriving Inhabited

-- Glass's delta (uses control group SD)
structure GlassDelta_F where val : Float deriving Repr, BEq, Inhabited
structure GlassDelta_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GlassDelta_R where val : ℝ     deriving Inhabited

-- Hedges' g (corrected Cohen's d)
structure HedgesG_F    where val : Float deriving Repr, BEq, Inhabited
structure HedgesG_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HedgesG_R    where val : ℝ     deriving Inhabited

-- Eta squared (η²)
structure EtaSquared_F where val : Float deriving Repr, BEq, Inhabited
structure EtaSquared_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EtaSquared_R where val : ℝ     deriving Inhabited

-- Partial eta squared
structure PartialEtaSq_F where val : Float deriving Repr, BEq, Inhabited
structure PartialEtaSq_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PartialEtaSq_R where val : ℝ     deriving Inhabited

-- Omega squared (ω²)
structure OmegaSquared_F where val : Float deriving Repr, BEq, Inhabited
structure OmegaSquared_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OmegaSquared_R where val : ℝ     deriving Inhabited

-- Cohen's f
structure CohensF_F    where val : Float deriving Repr, BEq, Inhabited
structure CohensF_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CohensF_R    where val : ℝ     deriving Inhabited

-- Cohen's f² (for multiple regression)
structure CohensF2_F   where val : Float deriving Repr, BEq, Inhabited
structure CohensF2_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CohensF2_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Regression and Model Fit
================================================================================================
-/
-- R-squared (coefficient of determination)
structure RSquared_F   where val : Float deriving Repr, BEq, Inhabited
structure RSquared_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RSquared_R   where val : ℝ     deriving Inhabited

-- Adjusted R-squared
structure AdjRSquared_F where val : Float deriving Repr, BEq, Inhabited
structure AdjRSquared_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AdjRSquared_R where val : ℝ     deriving Inhabited

-- Mean Squared Error
structure MSE_F        where val : Float deriving Repr, BEq, Inhabited
structure MSE_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MSE_R        where val : ℝ     deriving Inhabited

-- Root Mean Squared Error
structure RMSE_F       where val : Float deriving Repr, BEq, Inhabited
structure RMSE_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RMSE_R       where val : ℝ     deriving Inhabited

-- Mean Absolute Error
structure MAE_F        where val : Float deriving Repr, BEq, Inhabited
structure MAE_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MAE_R        where val : ℝ     deriving Inhabited

-- Residual
structure Residual_F   where val : Float deriving Repr, BEq, Inhabited
structure Residual_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Residual_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Information Criteria
================================================================================================
-/
-- Akaike Information Criterion
structure AIC_F        where val : Float deriving Repr, BEq, Inhabited
structure AIC_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AIC_R        where val : ℝ     deriving Inhabited

-- Corrected AIC (AICc)
structure AICc_F       where val : Float deriving Repr, BEq, Inhabited
structure AICc_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AICc_R       where val : ℝ     deriving Inhabited

-- Bayesian Information Criterion
structure BIC_F        where val : Float deriving Repr, BEq, Inhabited
structure BIC_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BIC_R        where val : ℝ     deriving Inhabited

-- Deviance Information Criterion
structure DIC_F        where val : Float deriving Repr, BEq, Inhabited
structure DIC_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DIC_R        where val : ℝ     deriving Inhabited

-- Watanabe-Akaike Information Criterion
structure WAIC_F       where val : Float deriving Repr, BEq, Inhabited
structure WAIC_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WAIC_R       where val : ℝ     deriving Inhabited

-- Leave-One-Out Cross-Validation score
structure LOO_F        where val : Float deriving Repr, BEq, Inhabited
structure LOO_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LOO_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Bayesian Statistics
================================================================================================
-/
-- Bayes factor
structure BayesFactor_F where val : Float deriving Repr, BEq, Inhabited
structure BayesFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BayesFactor_R where val : ℝ     deriving Inhabited

-- Log Bayes factor
structure LogBayesFactor_F where val : Float deriving Repr, BEq, Inhabited
structure LogBayesFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogBayesFactor_R where val : ℝ     deriving Inhabited

-- Posterior probability
structure Posterior_F  where val : Float deriving Repr, BEq, Inhabited
structure Posterior_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Posterior_R  where val : ℝ     deriving Inhabited

-- Prior probability
structure Prior_F      where val : Float deriving Repr, BEq, Inhabited
structure Prior_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Prior_R      where val : ℝ     deriving Inhabited

-- Likelihood
structure Likelihood_F where val : Float deriving Repr, BEq, Inhabited
structure Likelihood_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Likelihood_R where val : ℝ     deriving Inhabited

-- Log likelihood
structure LogLikelihood_F where val : Float deriving Repr, BEq, Inhabited
structure LogLikelihood_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogLikelihood_R where val : ℝ     deriving Inhabited

-- Likelihood ratio
structure LikelihoodRatio_F where val : Float deriving Repr, BEq, Inhabited
structure LikelihoodRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LikelihoodRatio_R where val : ℝ     deriving Inhabited

-- Credible interval bounds
structure CredibleInterval_F where
  lower : Float
  upper : Float
  level : Float  -- e.g., 0.95 for 95% CI
  deriving Repr, BEq, Inhabited

-- HPD interval (Highest Posterior Density)
structure HPDInterval_F where
  lower : Float
  upper : Float
  level : Float
  deriving Repr, BEq, Inhabited

/--
================================================================================================
   Confidence Intervals and Uncertainty
================================================================================================
-/
-- Confidence interval
structure ConfidenceInterval_F where
  lower : Float
  upper : Float
  level : Float  -- e.g., 0.95 for 95% CI
  deriving Repr, BEq, Inhabited

-- Confidence level
structure ConfidenceLevel_F where val : Float deriving Repr, BEq, Inhabited
structure ConfidenceLevel_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ConfidenceLevel_R where val : ℝ     deriving Inhabited

-- Margin of error
structure MarginOfError_F where val : Float deriving Repr, BEq, Inhabited
structure MarginOfError_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MarginOfError_R where val : ℝ     deriving Inhabited

-- Prediction interval
structure PredictionInterval_F where
  lower : Float
  upper : Float
  level : Float
  deriving Repr, BEq, Inhabited

-- Bootstrap CI
structure BootstrapCI_F where
  lower : Float
  upper : Float
  level : Float
  n_bootstrap : ℕ  -- Number of bootstrap samples
  deriving Repr, BEq, Inhabited

/--
================================================================================================
   Goodness of Fit Tests
================================================================================================
-/
-- Kolmogorov-Smirnov statistic
structure KSStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure KSStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KSStatistic_R where val : ℝ     deriving Inhabited

-- Anderson-Darling statistic
structure ADStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure ADStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ADStatistic_R where val : ℝ     deriving Inhabited

-- Shapiro-Wilk statistic
structure SWStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure SWStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SWStatistic_R where val : ℝ     deriving Inhabited

-- Jarque-Bera statistic
structure JBStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure JBStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JBStatistic_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Survival Analysis
================================================================================================
-/
-- Hazard ratio
structure HazardRatio_F where val : Float deriving Repr, BEq, Inhabited
structure HazardRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HazardRatio_R where val : ℝ     deriving Inhabited

-- Odds ratio
structure OddsRatio_F  where val : Float deriving Repr, BEq, Inhabited
structure OddsRatio_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OddsRatio_R  where val : ℝ     deriving Inhabited

-- Relative risk
structure RelativeRisk_F where val : Float deriving Repr, BEq, Inhabited
structure RelativeRisk_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelativeRisk_R where val : ℝ     deriving Inhabited

-- Number needed to treat
structure NNT_F        where val : Float deriving Repr, BEq, Inhabited
structure NNT_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NNT_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Meta-Analysis
================================================================================================
-/
-- Heterogeneity (I²)
structure ISquared_F   where val : Float deriving Repr, BEq, Inhabited
structure ISquared_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ISquared_R   where val : ℝ     deriving Inhabited

-- Tau squared (between-study variance)
structure TauSquared_F where val : Float deriving Repr, BEq, Inhabited
structure TauSquared_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TauSquared_R where val : ℝ     deriving Inhabited

-- Q statistic (Cochran's Q)
structure QStatistic_F where val : Float deriving Repr, BEq, Inhabited
structure QStatistic_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QStatistic_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Validation Helpers
================================================================================================
-/

-- Correlation must be between -1 and 1
def isValidCorrelation_F (r : PearsonCorr_F) : Bool :=
  -1.0 ≤ r.val && r.val ≤ 1.0

-- P-value must be between 0 and 1
def isValidPValue_F (p : PValue_F) : Bool :=
  0.0 ≤ p.val && p.val ≤ 1.0

-- Statistical significance check
def isSignificant_F (p : PValue_F) (alpha : Alpha_F) : Bool :=
  p.val < alpha.val

-- R-squared must be between 0 and 1
def isValidRSquared_F (r2 : RSquared_F) : Bool :=
  0.0 ≤ r2.val && r2.val ≤ 1.0

-- Probability validation
def isValidProbability_F (p : Float) : Bool :=
  0.0 ≤ p && p ≤ 1.0

-- Standard deviation must be non-negative
def isValidStdDev_F (sd : StdDev_F) : Bool :=
  sd.val ≥ 0.0

-- Variance must be non-negative
def isValidVariance_F (v : Variance_F) : Bool :=
  v.val ≥ 0.0

-- Chi-squared must be non-negative
def isValidChiSquared_F (chi2 : ChiSquared_F) : Bool :=
  chi2.val ≥ 0.0

-- Sample size must be positive
def isValidSampleSize (n : SampleSize) : Bool :=
  n.val > 0

-- Effect size interpretation (Cohen's d)
def interpretCohensD_F (d : CohensD_F) : String :=
  if d.val.abs < 0.2 then "negligible"
  else if d.val.abs < 0.5 then "small"
  else if d.val.abs < 0.8 then "medium"
  else "large"

-- Bayes factor interpretation (Jeffreys' scale)
def interpretBayesFactor_F (bf : BayesFactor_F) : String :=
  if bf.val < 1.0 then "evidence against H1"
  else if bf.val < 3.0 then "anecdotal evidence for H1"
  else if bf.val < 10.0 then "moderate evidence for H1"
  else if bf.val < 30.0 then "strong evidence for H1"
  else if bf.val < 100.0 then "very strong evidence for H1"
  else "decisive evidence for H1"

-- Power adequacy check
def isAdequatePower_F (power : Power_F) : Bool :=
  power.val ≥ 0.8  -- Standard threshold

-- Check if confidence interval contains value
def containsValue_F (ci : ConfidenceInterval_F) (value : Float) : Bool :=
  ci.lower ≤ value && value ≤ ci.upper

-- Check for practical significance
def isPracticallySignificant_F (effect : CohensD_F) (threshold : Float) : Bool :=
  effect.val.abs ≥ threshold

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Variance to standard deviation
def varianceToStdDev_F (v : Variance_F) : StdDev_F :=
  ⟨Float.sqrt v.val⟩

def stdDevToVariance_F (sd : StdDev_F) : Variance_F :=
  ⟨sd.val^2⟩

-- Standard error from standard deviation
def stdDevToStdError_F (sd : StdDev_F) (n : SampleSize) : StdError_F :=
  ⟨sd.val / Float.sqrt n.val.toFloat⟩

-- Z-score calculation
def toZScore_F (x : Float) (mean : Mean_F) (sd : StdDev_F) : ZScore_F :=
  ⟨(x - mean.val) / sd.val⟩

-- Percentile to quantile
def percentileToQuantile_F (p : Percentile_F) : Quantile_F :=
  { val := p.val, q := p.p / 100.0 }

def quantileToPercentile_F (q : Quantile_F) : Percentile_F :=
  { val := q.val, p := q.q * 100.0 }

-- Coefficient of variation
def coefficientOfVariation_F (sd : StdDev_F) (mean : Mean_F) : CoeffVar_F :=
  if mean.val == 0.0 then ⟨0.0⟩ else ⟨sd.val / mean.val.abs⟩

-- Power from Type II error
def betaToPower_F (beta : TypeIIError_F) : Power_F :=
  ⟨1.0 - beta.val⟩

def powerToBeta_F (power : Power_F) : TypeIIError_F :=
  ⟨1.0 - power.val⟩

-- Log transformations
def bayesFactorToLog_F (bf : BayesFactor_F) : LogBayesFactor_F :=
  ⟨Float.log bf.val⟩

def logToBayesFactor_F (lbf : LogBayesFactor_F) : BayesFactor_F :=
  ⟨Float.exp lbf.val⟩

def likelihoodToLogLikelihood_F (l : Likelihood_F) : LogLikelihood_F :=
  ⟨Float.log l.val⟩

def logLikelihoodToLikelihood_F (ll : LogLikelihood_F) : Likelihood_F :=
  ⟨Float.exp ll.val⟩

-- Odds ratio conversions
def probabilityToOdds_F (p : Float) : Float :=
  if p < 1.0 then p / (1.0 - p) else 1e308

def oddsToProbability_F (odds : Float) : Float :=
  odds / (1.0 + odds)

-- Chi-squared per degree of freedom
def chiSquaredToPerDF_F (chi2 : ChiSquared_F) (df : DegreesOfFreedom) : ChiSquaredPerDF_F :=
  ⟨chi2.val / df.val.toFloat⟩

-- Effect size conversions
def rToD_F (r : PearsonCorr_F) : CohensD_F :=
  ⟨2.0 * r.val / Float.sqrt (1.0 - r.val^2)⟩

def dToR_F (d : CohensD_F) : PearsonCorr_F :=
  ⟨d.val / Float.sqrt (d.val^2 + 4.0)⟩

def etaSquaredToF_F (eta2 : EtaSquared_F) : CohensF_F :=
  ⟨Float.sqrt (eta2.val / (1.0 - eta2.val))⟩

def fToEtaSquared_F (f : CohensF_F) : EtaSquared_F :=
  ⟨f.val^2 / (1.0 + f.val^2)⟩

-- RMSE from MSE
def mseToRmse_F (mse : MSE_F) : RMSE_F :=
  ⟨Float.sqrt mse.val⟩

def rmseToMse_F (rmse : RMSE_F) : MSE_F :=
  ⟨rmse.val^2⟩

/--
================================================================================================
   Common Statistical Calculations
================================================================================================
-/

-- Sample mean
def sampleMean_F (data : Array Float) : Mean_F :=
  if data.size > 0 then
    ⟨data.foldl (· + ·) 0.0 / data.size.toFloat⟩
  else
    ⟨0.0⟩

-- Sample variance (unbiased, n-1)
def sampleVariance_F (data : Array Float) : Variance_F :=
  if data.size > 1 then
    let mean := sampleMean_F data
    let sumSq := data.foldl (init := 0.0) fun acc x => acc + (x - mean.val)^2
    ⟨sumSq / (data.size - 1).toFloat⟩
  else
    ⟨0.0⟩

-- Sample standard deviation
def sampleStdDev_F (data : Array Float) : StdDev_F :=
  varianceToStdDev_F (sampleVariance_F data)

-- Skewness (moment-based)
def skewness_F (data : Array Float) : Skewness_F :=
  if data.size > 2 then
    let mean := sampleMean_F data
    let sd := sampleStdDev_F data
    let n := data.size.toFloat
    let sum3 := data.foldl (init := 0.0) fun acc x =>
      acc + ((x - mean.val) / sd.val)^3
    ⟨sum3 * n / ((n - 1.0) * (n - 2.0))⟩
  else
    ⟨0.0⟩

-- Kurtosis (excess kurtosis)
def excessKurtosis_F (data : Array Float) : ExcessKurtosis_F :=
  if data.size > 3 then
    let mean := sampleMean_F data
    let sd := sampleStdDev_F data
    let n := data.size.toFloat
    let sum4 := data.foldl (init := 0.0) fun acc x =>
      acc + ((x - mean.val) / sd.val)^4
    let g2 := sum4 / n - 3.0
    -- Fisher's correction for sample kurtosis
    ⟨g2 * (n + 1.0) * n / ((n - 1.0) * (n - 2.0) * (n - 3.0)) +
     3.0 * (n - 1.0)^2 / ((n - 2.0) * (n - 3.0))⟩
  else
    ⟨0.0⟩

-- Pearson correlation
def pearsonCorrelation_F (x : Array Float) (y : Array Float) : PearsonCorr_F :=
  if x.size ≠ y.size || x.size < 2 then
    ⟨0.0⟩
  else
    let mean_x := sampleMean_F x
    let mean_y := sampleMean_F y
    let n := x.size.toFloat

    let cov := (x.zip y).foldl (init := 0.0) fun acc (xi, yi) =>
      acc + (xi - mean_x.val) * (yi - mean_y.val)

    let var_x := x.foldl (init := 0.0) fun acc xi => acc + (xi - mean_x.val)^2
    let var_y := y.foldl (init := 0.0) fun acc yi => acc + (yi - mean_y.val)^2

    if var_x > 0.0 && var_y > 0.0 then
      ⟨cov / Float.sqrt (var_x * var_y)⟩
    else
      ⟨0.0⟩

-- Cohen's d (pooled standard deviation)
def cohensD_F (mean1 : Mean_F) (mean2 : Mean_F) (sd1 : StdDev_F) (sd2 : StdDev_F)
    (n1 : SampleSize) (n2 : SampleSize) : CohensD_F :=
  let pooledVar := ((n1.val - 1).toFloat * sd1.val^2 +
                    (n2.val - 1).toFloat * sd2.val^2) /
                   (n1.val + n2.val - 2).toFloat
  let pooledSD := Float.sqrt pooledVar
  if pooledSD > 0.0 then
    ⟨(mean1.val - mean2.val) / pooledSD⟩
  else
    ⟨0.0⟩

-- Glass's delta (uses control group SD)
def glassDelta_F (mean1 : Mean_F) (mean2 : Mean_F) (sd_control : StdDev_F) : GlassDelta_F :=
  if sd_control.val > 0.0 then
    ⟨(mean1.val - mean2.val) / sd_control.val⟩
  else
    ⟨0.0⟩

-- Hedges' g (bias-corrected Cohen's d)
def hedgesG_F (d : CohensD_F) (n1 : SampleSize) (n2 : SampleSize) : HedgesG_F :=
  let df := (n1.val + n2.val - 2).toFloat
  let correction := 1.0 - 3.0 / (4.0 * df - 1.0)
  ⟨d.val * correction⟩

-- T-statistic (two-sample)
def tStatistic_F (mean1 : Mean_F) (mean2 : Mean_F) (se_diff : StdError_F) : TStatistic_F :=
  if se_diff.val > 0.0 then
    ⟨(mean1.val - mean2.val) / se_diff.val⟩
  else
    ⟨0.0⟩

-- F-statistic
def fStatistic_F (var1 : Variance_F) (var2 : Variance_F) : FStatistic_F :=
  if var2.val > 0.0 then
    ⟨var1.val / var2.val⟩
  else
    ⟨1e308⟩  -- Large number approximating infinity

-- Chi-squared statistic for contingency table
def chiSquared_F (observed : Array (Array Float)) (expected : Array (Array Float))
    : ChiSquared_F :=
  let chi2 := observed.zip expected |>.foldl (init := 0.0) fun acc (obs_row, exp_row) =>
    obs_row.zip exp_row |>.foldl (init := acc) fun acc2 (o, e) =>
      if e > 0.0 then acc2 + (o - e)^2 / e else acc2
  ⟨chi2⟩

-- Cramér's V from chi-squared
def cramersV_F (chi2 : ChiSquared_F) (n : SampleSize) (min_dim : ℕ) : CramersV_F :=
  if n.val > 0 && min_dim > 1 then
    ⟨Float.sqrt (chi2.val / (n.val.toFloat * (min_dim - 1).toFloat))⟩
  else
    ⟨0.0⟩

-- R-squared from correlation
def rSquaredFromCorr_F (r : PearsonCorr_F) : RSquared_F :=
  ⟨r.val^2⟩

-- Adjusted R-squared
def adjustedRSquared_F (r2 : RSquared_F) (n : SampleSize) (k : ℕ) : AdjRSquared_F :=
  let n_float := n.val.toFloat
  let k_float := k.toFloat
  if n.val > k + 1 then
    ⟨1.0 - (1.0 - r2.val) * (n_float - 1.0) / (n_float - k_float - 1.0)⟩
  else
    ⟨r2.val⟩

-- AIC calculation
def aic_F (logLik : LogLikelihood_F) (k : ℕ) : AIC_F :=
  ⟨2.0 * k.toFloat - 2.0 * logLik.val⟩

-- AICc (corrected for small samples)
def aicc_F (aic : AIC_F) (k : ℕ) (n : SampleSize) : AICc_F :=
  if n.val > k + 1 then
    let correction := 2.0 * k.toFloat * (k.toFloat + 1.0) /
                     (n.val.toFloat - k.toFloat - 1.0)
    ⟨aic.val + correction⟩
  else
    ⟨aic.val⟩

-- BIC calculation
def bic_F (logLik : LogLikelihood_F) (k : ℕ) (n : SampleSize) : BIC_F :=
  ⟨k.toFloat * Float.log n.val.toFloat - 2.0 * logLik.val⟩

-- Bayes factor from BIC difference
def bayesFactorFromBIC_F (bic1 : BIC_F) (bic2 : BIC_F) : BayesFactor_F :=
  ⟨Float.exp ((bic2.val - bic1.val) / 2.0)⟩

-- Likelihood ratio test statistic
def likelihoodRatioTest_F (ll_null : LogLikelihood_F) (ll_alt : LogLikelihood_F)
    : ChiSquared_F :=
  ⟨2.0 * (ll_alt.val - ll_null.val)⟩

-- Confidence interval for mean (normal approximation)
def meanConfidenceInterval_F (mean : Mean_F) (se : StdError_F) (z : Float)
    : ConfidenceInterval_F :=
  { lower := mean.val - z * se.val
    upper := mean.val + z * se.val
    level := 0.95 }  -- Default to 95% CI

-- Margin of error
def marginOfError_F (se : StdError_F) (z : Float) : MarginOfError_F :=
  ⟨z * se.val⟩

-- Sample size for desired margin of error
def sampleSizeForMargin_F (sd : StdDev_F) (margin : MarginOfError_F) (z : Float)
    : SampleSize :=
  let n := (z * sd.val / margin.val)^2
  ⟨n.toUInt64.toNat + 1⟩

-- Power calculation (simplified for t-test)
def powerTTest_F (effect : CohensD_F) (n : SampleSize) (alpha : Alpha_F) : Power_F :=
  -- Simplified approximation using logistic function instead of tanh
  let ncp := effect.val * Float.sqrt (n.val.toFloat / 2.0)  -- Non-centrality parameter
  let z_alpha := 1.96  -- For alpha = 0.05, two-tailed
  let power := if ncp > z_alpha then
    let x := 0.7 * (ncp - z_alpha)
    let exp_x := Float.exp x
    0.5 + 0.5 * (exp_x - 1.0) / (exp_x + 1.0)  -- tanh approximation
  else
    alpha.val / 2.0
  ⟨power⟩

-- Sample size for desired power
def sampleSizeForPower_F (effect : CohensD_F) (power : Power_F) (alpha : Alpha_F)
    : SampleSize :=
  -- Simplified approximation
  let z_alpha := 1.96  -- For alpha = 0.05
  let z_beta := 0.84   -- For power = 0.80
  let n := 2.0 * ((z_alpha + z_beta) / effect.val)^2
  ⟨n.toUInt64.toNat + 1⟩

-- Helper: create indexed pairs recursively
def indexPValues (pvalues : List PValue_F) (idx : Nat) : List (Nat × PValue_F) :=
  match pvalues with
  | [] => []
  | p :: ps => (idx, p) :: indexPValues ps (idx + 1)

-- Helper: insertion sort for pairs
def insertPair (pair : Nat × PValue_F) (sorted : List (Nat × PValue_F))
    : List (Nat × PValue_F) :=
  match sorted with
  | [] => [pair]
  | x :: xs =>
    if pair.2.val < x.2.val then
      pair :: x :: xs
    else
      x :: insertPair pair xs

def sortPairs (pairs : List (Nat × PValue_F)) : List (Nat × PValue_F) :=
  match pairs with
  | [] => []
  | x :: xs => insertPair x (sortPairs xs)

-- False discovery rate (Benjamini-Hochberg) - full implementation
def fdrCorrection_F (pvalues : Array PValue_F) (alpha : Alpha_F)
    : Array (PValue_F × Bool) :=
  let n := pvalues.size
  if n == 0 then
    #[]
  else
    let m := n.toFloat
    -- Convert to list and create 1-indexed pairs
    let indexed := indexPValues pvalues.toList 1
    -- Sort by p-value
    let sorted := sortPairs indexed
    -- Apply BH correction
    let corrected := sorted.map fun (i, p) =>
      let threshold := alpha.val * i.toFloat / m
      (p, p.val ≤ threshold)
    corrected.toArray

-- Meta-analysis: fixed effects
def metaFixedEffects_F (effects : Array CohensD_F) (ses : Array StdError_F)
    : CohensD_F × StdError_F :=
  if effects.size ≠ ses.size || effects.size == 0 then
    (⟨0.0⟩, ⟨0.0⟩)
  else
    let weights := ses.map fun se => 1.0 / se.val^2
    let total_weight := weights.foldl (· + ·) 0.0
    let weighted_effect := (effects.zip weights).foldl (init := 0.0)
      fun acc (d, w) => acc + d.val * w
    let pooled_effect := weighted_effect / total_weight
    let pooled_se := Float.sqrt (1.0 / total_weight)
    (⟨pooled_effect⟩, ⟨pooled_se⟩)

-- Heterogeneity I²
def iSquared_F (q : QStatistic_F) (df : DegreesOfFreedom) : ISquared_F :=
  if q.val > df.val.toFloat then
    ⟨100.0 * (q.val - df.val.toFloat) / q.val⟩
  else
    ⟨0.0⟩

-- Number needed to treat
def nnt_F (risk_control : Float) (risk_treatment : Float) : NNT_F :=
  let arr := (risk_control - risk_treatment).abs  -- Absolute risk reduction
  if arr > 0.0 then
    ⟨1.0 / arr⟩
  else
    ⟨1e308⟩  -- Large number approximating infinity

-- Odds ratio
def oddsRatio_F (a b c d : Float) : OddsRatio_F :=
  -- 2x2 table: a,b / c,d
  if b > 0.0 && c > 0.0 then
    ⟨(a * d) / (b * c)⟩
  else
    ⟨1e308⟩  -- Large number approximating infinity

-- Relative risk
def relativeRisk_F (a b c d : Float) : RelativeRisk_F :=
  -- 2x2 table: a,b / c,d
  let risk1 := a / (a + b)
  let risk2 := c / (c + d)
  if risk2 > 0.0 then
    ⟨risk1 / risk2⟩
  else
    ⟨1e308⟩  -- Large number approximating infinity

end Units.Stats
