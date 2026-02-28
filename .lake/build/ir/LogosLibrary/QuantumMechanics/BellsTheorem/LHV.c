// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.BellsTheorem.LHV
// Imports: Init Mathlib.MeasureTheory.Integral.Bochner.Basic Mathlib.MeasureTheory.Measure.ProbabilityMeasure Mathlib.Probability.Independence.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real
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
LEAN_EXPORT lean_object* l_BellTheorem_instCoeFunResponseFunctionForallReal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BellTheorem_instCoeFunResponseFunctionForallReal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BellTheorem_instCoeFunResponseFunctionForallReal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BellTheorem_instCoeFunResponseFunctionForallReal___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BellTheorem_instCoeFunResponseFunctionForallReal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_BellTheorem_instCoeFunResponseFunctionForallReal___lam__0), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BellTheorem_instCoeFunResponseFunctionForallReal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BellTheorem_instCoeFunResponseFunctionForallReal(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_Bochner_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_ProbabilityMeasure(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Probability_Independence_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_LHV(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_Bochner_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_ProbabilityMeasure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Probability_Independence_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
