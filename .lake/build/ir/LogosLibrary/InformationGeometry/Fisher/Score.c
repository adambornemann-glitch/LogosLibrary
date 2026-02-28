// Lean compiler output
// Module: LogosLibrary.InformationGeometry.Fisher.Score
// Imports: public import Init public import LogosLibrary.InformationGeometry.Fisher.StatisticalModel public import Mathlib.Analysis.Calculus.ParametricIntegral public import Mathlib.Topology.MetricSpace.Basic public import Mathlib.Analysis.Normed.Operator.Basic public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_InformationGeometry_Fisher_StatisticalModel(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_ParametricIntegral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Operator_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Function_StronglyMeasurable_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_InformationGeometry_Fisher_Score(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_InformationGeometry_Fisher_StatisticalModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_ParametricIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_MetricSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Operator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Function_StronglyMeasurable_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
