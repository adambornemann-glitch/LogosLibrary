// Lean compiler output
// Module: LogosLibrary.Superior.NanoThermo.Definition
// Imports: Init LogosLibrary.Superior.ThermalTime Mathlib.Analysis.SpecialFunctions.Log.Basic
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
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NanoThermodynamics_Definition_mutualInformation(lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NanoThermodynamics_Definition_mutualInformation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_ThermalTime(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_NanoThermo_Definition(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_ThermalTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
