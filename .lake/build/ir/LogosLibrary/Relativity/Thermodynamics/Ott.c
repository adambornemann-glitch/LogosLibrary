// Lean compiler output
// Module: LogosLibrary.Relativity.Thermodynamics.Ott
// Imports: public import Init public import LogosLibrary.Relativity.GR.KerrMetric public import Mathlib.Analysis.SpecialFunctions.Log.Basic public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_freeEnergy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_twoStateOmega;
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_freeEnergy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_Unification_landsbergTransform___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_logos__library_RelativisticTemperature_Unification_landsbergTransform(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_up_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_logos__library_RelativisticTemperature_RelativeEntropy_TwoState_down_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_lp_logos__library_RelativisticTemperature_RelativeEntropy_twoStateOmega(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_logos__library_LogosLibrary_Relativity_GR_KerrMetric(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_logos__library_LogosLibrary_Relativity_Thermodynamics_Ott(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_logos__library_LogosLibrary_Relativity_GR_KerrMetric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_logos__library_RelativisticTemperature_RelativeEntropy_twoStateOmega = _init_lp_logos__library_RelativisticTemperature_RelativeEntropy_twoStateOmega();
lean_mark_persistent(lp_logos__library_RelativisticTemperature_RelativeEntropy_twoStateOmega);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
