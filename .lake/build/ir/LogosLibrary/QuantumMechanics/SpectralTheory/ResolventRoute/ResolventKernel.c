// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.ResolventKernel
// Imports: Init LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute
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
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPoint___redArg(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPoint(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
lean_object* l_Complex_ofReal(lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPointNeg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPointNeg___redArg(lean_object*, lean_object*);
extern lean_object* l_Complex_I;
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Complex_ofReal(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Complex_I;
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Complex_ofReal(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_7);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_7);
lean_inc(x_8);
lean_inc(x_5);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_8);
x_15 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_8);
x_18 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_7);
x_19 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_16);
x_21 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_21, 0, x_12);
lean_closure_set(x_21, 1, x_19);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_4);
x_24 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_24, 0, x_4);
lean_closure_set(x_24, 1, x_7);
lean_inc(x_8);
lean_inc(x_5);
x_25 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_8);
x_26 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_28, 0, x_4);
lean_closure_set(x_28, 1, x_8);
x_29 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_29, 0, x_5);
lean_closure_set(x_29, 1, x_7);
x_30 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_31, 0, x_22);
lean_closure_set(x_31, 1, x_27);
x_32 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_32, 0, x_23);
lean_closure_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_SpectralBridge_Resolvent_offRealPoint___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPointNeg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Complex_ofReal(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Complex_I;
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Complex_ofReal(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_7);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_7);
lean_inc(x_8);
lean_inc(x_5);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_8);
x_15 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_8);
x_18 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_7);
x_19 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_20, 0, x_16);
x_21 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_22, 0, x_19);
x_23 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_22);
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_4);
x_26 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_7);
lean_inc(x_8);
lean_inc(x_5);
x_27 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_27, 0, x_5);
lean_closure_set(x_27, 1, x_8);
x_28 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_29, 0, x_26);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_30, 0, x_4);
lean_closure_set(x_30, 1, x_8);
x_31 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_31, 0, x_5);
lean_closure_set(x_31, 1, x_7);
x_32 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_33, 0, x_29);
x_34 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_34, 0, x_24);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_35, 0, x_32);
x_36 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_36, 0, x_25);
lean_closure_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_SpectralBridge_Resolvent_offRealPointNeg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_SpectralBridge_Resolvent_offRealPointNeg___redArg(x_1, x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Bochner(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_BochnerRoute(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_ResolventRoute_ResolventKernel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Bochner(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_UnitaryEvo_Resolvent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_SpectralTheory_BochnerRoute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
