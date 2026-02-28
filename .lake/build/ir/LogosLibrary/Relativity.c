// Lean compiler output
// Module: LogosLibrary.Relativity
// Imports: Init LogosLibrary.Relativity.GR.KerrMetric LogosLibrary.Relativity.GR.SdS.Bornemann LogosLibrary.Relativity.SR.MinkowskiSpacetime LogosLibrary.Relativity.Thermodynamics.Jacobson LogosLibrary.Relativity.Thermodynamics.Ott LogosLibrary.Relativity.Thermodynamics.ConnesRovelli
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
lean_object* initialize_LogosLibrary_Relativity_GR_KerrMetric(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Relativity_GR_SdS_Bornemann(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Relativity_SR_MinkowskiSpacetime(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Relativity_Thermodynamics_Jacobson(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Relativity_Thermodynamics_Ott(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Relativity_Thermodynamics_ConnesRovelli(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Relativity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Relativity_GR_KerrMetric(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Relativity_GR_SdS_Bornemann(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Relativity_SR_MinkowskiSpacetime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Relativity_Thermodynamics_Jacobson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Relativity_Thermodynamics_Ott(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Relativity_Thermodynamics_ConnesRovelli(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
