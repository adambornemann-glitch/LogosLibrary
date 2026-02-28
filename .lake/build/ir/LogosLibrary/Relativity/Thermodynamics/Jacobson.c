// Lean compiler output
// Module: LogosLibrary.Relativity.Thermodynamics.Jacobson
// Imports: public import Init public import LogosLibrary.Relativity.Thermodynamics.Ott
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
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_logos__library_Jacobson_unruhTempLandsberg___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_Jacobson_unruhTempLandsberg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_logos__library_Jacobson_unruhTempLandsberg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_Relativity_Thermodynamics_Ott(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_Relativity_Thermodynamics_Jacobson(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_Relativity_Thermodynamics_Ott(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
