// Lean compiler output
// Module: LogosLibrary.Superior.Strings.Basic
// Imports: public import Init public import Mathlib.Analysis.SpecialFunctions.Pow.Real public import Mathlib.Analysis.SpecialFunctions.Sqrt public import Mathlib.Analysis.Real.Pi.Bounds
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
LEAN_EXPORT lean_object* lp_logos__library_SuperiorString_Basic_D__spatial;
LEAN_EXPORT lean_object* lp_logos__library_SuperiorString_Basic_n__transverse;
static lean_object* _init_lp_logos__library_SuperiorString_Basic_D__spatial(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
static lean_object* _init_lp_logos__library_SuperiorString_Basic_n__transverse(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Sqrt(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Real_Pi_Bounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_Superior_Strings_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Sqrt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Real_Pi_Bounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_logos__library_SuperiorString_Basic_D__spatial = _init_lp_logos__library_SuperiorString_Basic_D__spatial();
lean_mark_persistent(lp_logos__library_SuperiorString_Basic_D__spatial);
lp_logos__library_SuperiorString_Basic_n__transverse = _init_lp_logos__library_SuperiorString_Basic_n__transverse();
lean_mark_persistent(lp_logos__library_SuperiorString_Basic_n__transverse);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
