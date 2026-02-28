// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.ModularTheory.KMS.PeriodicStrip
// Imports: Init Mathlib.Analysis.Complex.Basic Mathlib.Analysis.Complex.Liouville Mathlib.Analysis.Calculus.FDeriv.Basic Mathlib.Topology.ContinuousOn Mathlib.Algebra.Order.Floor.Defs Mathlib.Algebra.Order.Floor.Ring Mathlib.Algebra.Order.Floor.Semiring Mathlib.Algebra.Order.Floor.Div Mathlib.Algebra.Order.Floor.Semifield Mathlib.Analysis.SpecialFunctions.Complex.Log Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Analysis.Complex.RemovableSingularity
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
LEAN_EXPORT lean_object* l_realToUpper(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
lean_object* l_Complex_ofReal(lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Complex_I;
LEAN_EXPORT lean_object* l_realToLower(lean_object*);
LEAN_EXPORT lean_object* l_realToLower(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Complex_ofReal(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_realToUpper(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Complex_ofReal(x_1);
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
x_9 = l_Complex_ofReal(x_2);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Liouville(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_FDeriv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_ContinuousOn(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Floor_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Floor_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Floor_Semiring(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Floor_Div(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Floor_Semifield(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Complex_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_CauchyIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_RemovableSingularity(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_ModularTheory_KMS_PeriodicStrip(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Liouville(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_FDeriv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_ContinuousOn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Floor_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Floor_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Floor_Semiring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Floor_Div(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Floor_Semifield(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Complex_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_CauchyIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_RemovableSingularity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
