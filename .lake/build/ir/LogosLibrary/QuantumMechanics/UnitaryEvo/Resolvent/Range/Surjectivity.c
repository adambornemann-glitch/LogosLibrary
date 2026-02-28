// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.Surjectivity
// Imports: public import Init public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.Orthogonal public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.ClosedRange
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
LEAN_EXPORT lean_object* lp_logos__library_QuantumMechanics_Resolvent_rangeSubmodule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_QuantumMechanics_Resolvent_rangeSubmodule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_QuantumMechanics_Resolvent_rangeSubmodule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_logos__library_QuantumMechanics_Resolvent_rangeSubmodule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_logos__library_QuantumMechanics_Resolvent_rangeSubmodule(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range_Orthogonal(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range_ClosedRange(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range_Surjectivity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range_Orthogonal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range_ClosedRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
