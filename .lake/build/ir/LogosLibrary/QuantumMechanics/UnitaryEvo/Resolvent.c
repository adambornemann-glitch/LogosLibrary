// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
// Imports: public import Init public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Basic public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.LowerBound public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.NormExpansion public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.SpecialCases public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Core public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Identities public import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Analytic
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
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Basic(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_LowerBound(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_NormExpansion(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_SpecialCases(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Core(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Identities(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Analytic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_LowerBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_NormExpansion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_SpecialCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Identities(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent_Analytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
