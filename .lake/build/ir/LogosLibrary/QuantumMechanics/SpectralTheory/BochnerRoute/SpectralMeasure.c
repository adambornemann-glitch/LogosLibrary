// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.SpectralMeasure
// Imports: Init Mathlib.Analysis.InnerProductSpace.Basic Mathlib.MeasureTheory.Measure.Stieltjes Mathlib.MeasureTheory.Measure.MeasureSpace LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_Stieltjes(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_MeasureSpace(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Bochner(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_BochnerRoute_SpectralMeasure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_Stieltjes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_MeasureSpace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Bochner(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
