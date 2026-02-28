// Lean compiler output
// Module: LogosLibrary.InformationGeometry.Fisher.FisherMetric
// Imports: public import Init public import LogosLibrary.InformationGeometry.Fisher.FisherInformation public import Mathlib.LinearAlgebra.BilinearMap public import Mathlib.Analysis.Calculus.ContDiff.Defs
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_InformationGeometry_RiemannianMetric_eval___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0___closed__0 = (const lean_object*)&lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0___closed__0_value;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_InformationGeometry_RiemannianMetric_eval___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_InformationGeometry_RiemannianMetric_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_InformationGeometry_RiemannianMetric_eval___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_7 = lean_apply_1(x_1, x_2);
lean_inc(x_6);
x_8 = lean_apply_1(x_3, x_6);
x_9 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_apply_3(x_4, x_5, x_2, x_6);
x_11 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0___closed__0));
x_3 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_4 = l_List_foldrTR___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_2, x_1);
x_4 = lp_logos__library_Multiset_sum___at___00Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_logos__library_InformationGeometry_RiemannianMetric_eval___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(lp_logos__library_InformationGeometry_RiemannianMetric_eval___lam__0), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_4);
x_8 = lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_logos__library_InformationGeometry_RiemannianMetric_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_List_finRange(x_1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(lp_logos__library_InformationGeometry_RiemannianMetric_eval___lam__1), 6, 5);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_6);
x_8 = lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_logos__library_Finset_sum___at___00InformationGeometry_RiemannianMetric_eval_spec__0___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_InformationGeometry_Fisher_FisherInformation(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_BilinearMap(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_ContDiff_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_InformationGeometry_Fisher_FisherMetric(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_InformationGeometry_Fisher_FisherInformation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_BilinearMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_ContDiff_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
